/*
 * z3plus.h
 * rainoftime@gmail.com
 */

#ifndef Z3PLUS_H_
#define Z3PLUS_H_
#include <vector>
#include <set>
#include <future>
#include <map>
#include <iostream>
#include <memory>
#include <set>
#include <vector>
#include <algorithm>
#include "z3++.h"
#include "z3.h"
using namespace z3;
/*
 * We provide the following APIs
 *  - get_expr_vars(exp, vars)
 *      get all variables of exp and store in vars
 *  - get_vars_differenct(vars_a, vars_b)
 *      set differences of vars_a and vars_b
 *  - get_k_modles(exp, k)
 *      use the solver to get k models
 *  - get_abstract_interval(pre_cond, query)
 *      get the interval of query, under the condition pre_cond
 *  - get_abstract_interval_as_expr
 *      get the result as a z3 expr
 *  - do_constant_propagation(exp)
 *      use cp to simplify exp
 */

bool get_expr_vars(expr& exp, expr_vector& vars) {
    // TODO: test the efficiency of this function
    try {
        auto& ctx = exp.ctx();
        auto compare_func = [](const z3::expr& a, const z3::expr& b) {
            Z3_symbol sym_a = a.decl().name();
            Z3_symbol sym_b = b.decl().name();
            return sym_a < sym_b;
        };
        std::set<z3::expr, decltype(compare_func)> syms(compare_func);
        std::function<void(const z3::expr&)> recur = [&recur, &syms, &ctx](
                const z3::expr& e) {
            assert(Z3_is_app(ctx, e));
            auto app = Z3_to_app(ctx, e);
            unsigned n_args = Z3_get_app_num_args(ctx, app);

            auto fdecl = Z3_get_app_decl(ctx, app);
            if (n_args == 0 && Z3_get_decl_kind(ctx, fdecl) == Z3_OP_UNINTERPRETED)
                syms.insert(e);

            for (unsigned i = 0; i < n_args; ++i) {
                z3::expr arg(ctx, Z3_get_app_arg(ctx, app, i));
                recur(arg);
            }
        };
        recur(exp);
        // if the return type is std::vector<z3::expr>
        //return std::vector<z3::expr>(syms.begin(), syms.end());;
        for (auto& i : syms) {
            vars.push_back(i);
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return false;
    }
    return true;
}
// note that we assume vars_a and vars_b consist of purely variables.
expr_vector get_vars_difference(expr_vector& vars_a, expr_vector& vars_b) {
    expr_vector ret(vars_a.ctx());
    try {
        for (unsigned i = 0; i < vars_a.size(); i++) {
            bool is_in_diff = true;
            Z3_symbol sym_i = vars_a[i].decl().name();
            for (unsigned j = 0; j < vars_b.size(); j++) {
                if (sym_i == vars_b[j].decl().name()) { is_in_diff = false; }
            }
            if (is_in_diff) { ret.push_back(vars_a[i]); }
        }
    } catch (z3::exception & ex) {
        std::cout << ex.msg() << std::endl;
        return ret;
    }
    return ret;
}
// TODO: store the models
void get_k_models(z3::expr& exp, int k) {
    z3::context& ctx = exp.ctx();
    z3::solver solver(ctx);
    solver.add(exp);
    while (solver.check() == z3::sat && k >= 1) {
        std::cout << solver << std::endl;
        // get model
        z3::model m = solver.get_model();
        z3::expr_vector args(ctx);
        for (unsigned i = 0; i < m.size(); i++) {
            // get z3 variable
            z3::func_decl z3Variable = m[i];
            std::string varName = z3Variable.name().str();
            z3::expr exp = m.get_const_interp(z3Variable);
            unsigned bvSize = exp.get_sort().bv_size();
            int value = m.eval(exp).get_numeral_int();
            // std::string svalue = Z3_get_numeral_string(ctx, exp);
            // uniq result
            if (exp.get_sort().is_bv()) {
                //args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(svalue.c_str(), bvSize));
                args.push_back(ctx.bv_const(varName.c_str(), bvSize) != ctx.bv_val(value, bvSize));
            }
        }
        // block current model
        solver.add(mk_or(args));
        k--;
    }
}

std::pair<int, int> get_abstract_interval(expr& pre_cond, expr& query, int timeout=3000) {
    // TODO: should we return an Expr or a domain value(like [a, b])
    z3::context &c = pre_cond.ctx();
    std::pair<int, int> ret(INT_MIN, INT_MAX);
    z3::optimize opt1(c);
    z3::optimize opt2(c);
    z3::params p(c);
    p.set("priority", c.str_symbol("pareto"));
    z3::set_param("smt.timeout", timeout);
    //p.set("timeout", Timeout); TODO: it seems we cannot set timeout directly to opt
    opt1.set(p); opt2.set(p);
    opt1.add(pre_cond);
    z3::optimize::handle h1 = opt1.maximize(query);
    opt2.add(pre_cond);
    z3::optimize::handle h2 = opt2.minimize(query);
    try {
        if (opt1.check() == z3::sat) {
            //std::cout << __LINE__ << std::endl;
            //std::cout << opt1.get_model() << std::endl;
            ret.second = opt1.lower(h1).get_numeral_int();
            //std::cout << __LINE__ << std::endl;
        }
    } catch (z3::exception &ex) {
        std::cout << ex << std::endl;
    }
    try {
        if (opt2.check() == z3::sat) {
            //std::cout << __LINE__ << std::endl;
            //std::cout << opt1.upper(h2) << std::endl;
            ret.first = opt2.upper(h2).get_numeral_int();
            //std::cout << __LINE__ << std::endl;
        }
    } catch (z3::exception &ex) {
        std::cout << ex << std::endl;
    }
    return ret;
}

void get_abstract_interval_as_expr(expr& pre_cond, expr& query, expr_vector& res, int timeout=3000) {
    context &Ctx = pre_cond.ctx();
    params Param(Ctx);
    Param.set("priority", Ctx.str_symbol("pareto"));
    set_param("smt.timeout", timeout);
    //p.set("timeout", Timeout); TODO: it seems we cannot set timeout directly to opt
    optimize UpperFinder(Ctx);
    optimize LowerFinder(Ctx);
    UpperFinder.set(Param); LowerFinder.set(Param);
    UpperFinder.add(pre_cond);
    optimize::handle UpperGoal = UpperFinder.maximize(query);
    LowerFinder.add(pre_cond);
    optimize::handle LowerGoal = LowerFinder.minimize(query);
    try {
        if (LowerFinder.check() == z3::sat) {
            //std::cout << "Find lower success\n";
            res.push_back(LowerFinder.upper(LowerGoal));
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }
    try {
        if (UpperFinder.check() == z3::sat) {
            //std::cout << "Find upper success\n";
            res.push_back(UpperFinder.lower(UpperGoal));
        }
    } catch(z3::exception &Ex) {
        res.push_back(Ctx.bool_val(false));
    }
}

expr do_constant_propagation(expr& to_simp) {
    goal gg(to_simp.ctx());
    gg.add(to_simp);
    tactic cp = tactic(to_simp.ctx(), "propagate-values");
    return cp.apply(gg)[0].as_expr();
}

#endif /* Z3PLUS_H_ */
