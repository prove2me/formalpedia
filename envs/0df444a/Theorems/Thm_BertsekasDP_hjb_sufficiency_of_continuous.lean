-- Prove2me | Theorems.Thm_BertsekasDP_hjb_sufficiency_of_continuous
-- name    : BertsekasDP.hjb_sufficiency_of_continuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T22:01:02.481478+00:00
-- url     : https://prove2.me/theorems/9801c100-0ccb-4d7c-9ca0-ad9285d09666
-- title:
--   HJB sufficiency theorem (Prop. 3.2.1), with continuous $f$ and $g$
-- statement:
--   **Proposition 3.2.1 (Sufficiency Theorem for the HJB equation).** Consider the continuous-time problem of minimizing $h(x(T)) + \int g(x,u)\,dt$ subject to $\dot x = f(x,u)$ and $u(t) \in U$, with the system function $f$ and the running cost $g$ **continuous**. Suppose $V(t,x)$ is continuously differentiable and solves the Hamilton–Jacobi–Bellman equation: for every $t \in [0,T]$ and every state $x$,
--
--   $$0 \;=\; \min_{u \in U} \Bigl[\, g(x,u) \;+\; \partial_t V(t,x) \;+\; \bigl\langle \nabla_x V(t,x), \, f(x,u) \bigr\rangle \,\Bigr],$$
--
--   with the boundary condition $V(T,x) = h(x)$. Then:
--
--   1. **$V$ is a lower bound on the cost-to-go.** For every start $(t_0,\xi)$ with $t_0 \in [0,T]$ and every admissible control/state pair $(u,x)$ on $[t_0,T]$ with $x(t_0) = \xi$,
--   $$V(t_0,\xi) \;\le\; h\bigl(x(T)\bigr) + \int_{t_0}^{T} g\bigl(x(t),u(t)\bigr)\,dt .$$
--   2. **A trajectory attaining the minimum is optimal.** If an admissible pair $(u^*,x^*)$ from $(t_0,\xi)$ satisfies the HJB expression with equality at every time — that is, $u^*(t)$ attains the minimum above along $x^*(t)$ — then its cost equals $V(t_0,\xi)$ exactly.
--
--   Together the two parts say that a classical solution of the HJB equation *is* the optimal cost-to-go function and that greedy minimization against it yields an optimal control. This is the verification direction of dynamic programming in continuous time: hard to apply when $V$ is unknown, decisive when a candidate $V$ can be guessed, as for the linear-quadratic problem.
--
--   **On the regularity hypotheses.** The source's standing assumptions for Chapter 3 (§3.1) are that $f$ and $g$ are continuously differentiable in $x$ and continuous in $u$. The proof of the sufficiency theorem uses only one consequence of this: that the running cost $g(x(t),u(t))$ and the velocity $f(x(t),u(t))$ are integrable along every admissible trajectory, so that the differential inequality $\tfrac{d}{dt}V(t,x(t)) \ge -g(x(t),u(t))$ can be integrated. Joint continuity of $f$ and $g$ delivers exactly that (a continuous function of a continuous state and a bounded, piecewise continuous control is bounded and continuous off finitely many times), so it is the hypothesis assumed here. It supersedes an earlier statement of this proposition on the platform that carried no regularity hypothesis at all and was disproved: with a discontinuous $g$ the cost integrand need not be integrable, and the integral then takes the library's junk value $0$.
--
--   **Formalization Note** The HJB condition is stated as "$0$ is the greatest lower bound" of the bracketed set over $u \in U$, so the minimum need not be attained; if $U$ is empty the hypothesis is unsatisfiable and the theorem is vacuous. Admissible controls take values in $U$ on $[t_0,T]$, have bounded image there, and are continuous off a finite set; state trajectories are continuous and satisfy the system equation off a finite set. Under these hypotheses the cost integral is a genuine integral, never the junk value. The statement is about a *given* $V$: it does not assert that such a $V$ exists, nor that an optimal control exists. Part 2 requires the equality at every time of the interval, with no exceptional set.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 3.2.1 (Sufficiency Theorem), Section 3.2; regularity of f and g per the standing assumptions of Section 3.1, p. 107 ("f is continuously differentiable with respect to x and is continuous with respect to u"; "g and h are continuously differentiable with respect to x, and g is continuous with respect to u"), of which joint continuity is the part the sufficiency proof uses

import Mathlib
import Definitions.Def_BertsekasCTModel

namespace BertsekasDP

open scoped RealInnerProductSpace

theorem hjb_sufficiency_of_continuous {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : Continuous (Function.uncurry M.f))
    (hg : Continuous (Function.uncurry M.g))
    (V : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hV : ContDiff ℝ 1 (Function.uncurry V))
    (hHJB : ∀ t ∈ Set.Icc 0 M.T, ∀ x : EuclideanSpace ℝ (Fin n),
      IsGLB ((fun u => M.g x u + deriv (fun s => V s x) t +
        ⟪gradient (V t) x, M.f x u⟫) '' M.U) 0)
    (hbdry : ∀ x, V M.T x = M.h x) :
    (∀ t₀ ∈ Set.Icc 0 M.T, ∀ ξ u x,
      BertsekasCTAdmissibleFrom M t₀ ξ u x →
        V t₀ ξ ≤ BertsekasCTCostFrom M t₀ u x) ∧
    (∀ t₀ ∈ Set.Icc 0 M.T, ∀ ξ ustar xstar,
      BertsekasCTAdmissibleFrom M t₀ ξ ustar xstar →
      (∀ t ∈ Set.Icc t₀ M.T,
        M.g (xstar t) (ustar t) + deriv (fun s => V s (xstar t)) t +
          ⟪gradient (V t) (xstar t), M.f (xstar t) (ustar t)⟫ = 0) →
        BertsekasCTCostFrom M t₀ ustar xstar = V t₀ ξ) := by sorry

end BertsekasDP
