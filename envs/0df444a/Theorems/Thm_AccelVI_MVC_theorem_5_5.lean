-- Prove2me | Theorems.Thm_AccelVI_MVC_theorem_5_5
-- name    : AccelVI.MVC.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:35.228273+00:00
-- url     : https://prove2.me/theorems/41ca7ea5-8227-46fa-b1cd-380aa1ce1e91
-- title:
--   Theorem 5.5, p. 10 — for a reversible policy chain, M-VC converges to v^π with v_s = v^π + o(((1 − √(1/κ))/(1 + √(1/κ)) + η)^s) for every η > 0
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a finite MDP with discount factor $\lambda \in (0,1)$, and let $\pi$ be a policy whose transition matrix $L_\pi$ defines an irreducible, reversible Markov chain on $S$. Let $(v_s)_{s \ge 0}$ be the iterates of Momentum Value Computation
--   $$v_{s+1} = v_s - \alpha\,(v_s - T_\pi(v_s)) + \beta\,(v_s - v_{s-1}), \qquad s \ge 1,$$
--   with the constant step sizes (4.2), $\alpha = 2/(1+\sqrt{1-\lambda^2})$ and $\beta = (1-\sqrt{1-\lambda^2})/(1+\sqrt{1-\lambda^2})$, started from arbitrary $v_0, v_1 \in \mathbb{R}^n$. Write $\kappa = (1+\lambda)/(1-\lambda)$. Then:
--
--   1. $(v_s)_{s \ge 0}$ converges to the value function $v^\pi$;
--   2. for every $\eta > 0$,
--   $$v_s = v^\pi + o\!\left(\left(\frac{1-\sqrt{1/\kappa}}{1+\sqrt{1/\kappa}} + \eta\right)^{s}\right) \quad (s \to \infty);$$
--   3. $0 < \dfrac{1-\sqrt{1/\kappa}}{1+\sqrt{1/\kappa}} < \lambda$.
--
--   Momentum Value Computation therefore converges geometrically at a rate strictly better than the rate $\lambda$ of Value Computation, and slightly better than the rate $1 - \sqrt{1/\kappa}$ of Accelerated Value Computation.
--
--   **Formalization Note.** The norm on $\mathbb{R}^n$ is the sup norm $\|\cdot\|_\infty$ (Mathlib's norm on `S → ℝ`); the little-o is with respect to it as $s \to \infty$. The value function is the Neumann series $\sum_t \lambda^t L_\pi^t r_\pi$. "Irreducible, reversible" means irreducible plus a stationary probability distribution in detailed balance (Definition 2.1).
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 10, Theorem 5.5; proof p. 22 (combining Lemma B.1 with Lemma B.2)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Theorem 5.5, p. 10: if π defines an irreducible, reversible Markov chain, the M-VC iterates with step
sizes (4.2) converge to v^π, v_s = v^π + o(((1 − √(1/κ))/(1 + √(1/κ)) + η)^s) for every η > 0, and
0 < (1 − √(1/κ))/(1 + √(1/κ)) < λ. -/
theorem theorem_5_5 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) (v0 v1 : S → ℝ) :
    Filter.Tendsto (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1) Filter.atTop (nhds (valuePol M pol)) ∧
    (∀ η : ℝ, 0 < η →
      (fun s => mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s - valuePol M pol)
        =o[Filter.atTop] (fun s => (rateMVC M.lam + η) ^ s)) ∧
    0 < rateMVC M.lam ∧ rateMVC M.lam < M.lam := by sorry

end AccelVI.MVC
