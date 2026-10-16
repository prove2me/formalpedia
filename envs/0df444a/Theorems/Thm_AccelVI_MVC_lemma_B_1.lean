-- Prove2me | Theorems.Thm_AccelVI_MVC_lemma_B_1
-- name    : AccelVI.MVC.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:40.04761+00:00
-- url     : https://prove2.me/theorems/99198fac-3f0d-4b08-8f11-045eaebbbefe
-- title:
--   Lemma B.1, p. 21 — x_s = x^π + B_π^{s−1}(x_1 − x^π) for all s ≥ 1 (x_1 for the printed, undefined x_0)
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a valid finite MDP and $\pi$ a policy, with value function $v^\pi$. Let $(v_s)_{s \ge 0}$ be the iterates of Momentum Value Computation with the step sizes (4.2), started from arbitrary $v_0, v_1 \in \mathbb{R}^n$, and let $B_\pi$ be the $2n \times 2n$ matrix of App. B. Put
--   $$x^\pi = (v^\pi, v^\pi) \in \mathbb{R}^{2n}, \qquad x_s = (v_s, v_{s-1}) \in \mathbb{R}^{2n} \quad (s \ge 1).$$
--   Then
--   $$x_s = x^\pi + B_\pi^{\,s-1}\,(x_1 - x^\pi) \qquad \text{for all } s \ge 1 .$$
--
--   The lemma reduces the convergence of M-VC to the behaviour of the powers of the single matrix $B_\pi$.
--
--   **Formalization Note.** The paper prints $x_0 - x^\pi$ on the right-hand side; $x_0 = (v_0, v_{-1})$ is undefined since there is no $v_{-1}$, and at $s = 1$ the identity forces the vector to be $x_1 - x^\pi$, so the statement uses $x_1 = (v_1, v_0)$, matching the analogous Lemma 5.2 for A-VC. Pairs are functions on $S \oplus S$ (`Sum.elim`), the first copy holding the newer iterate.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 21, Lemma B.1 (printed x_0 read as x_1)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma B.1, p. 21 (with x₁ for the printed, undefined x₀): for the M-VC iterates with step sizes (4.2),
x_s = (v_s, v_{s−1}) satisfies x_s = x^π + B_π^{s−1}(x₁ − x^π) for all s ≥ 1, where x^π = (v^π, v^π). -/
theorem lemma_B_1 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol)
    (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    Sum.elim (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 s)
        (mvc M pol (alphaMVC M.lam) (betaMVC M.lam) v0 v1 (s - 1)) =
      Sum.elim (valuePol M pol) (valuePol M pol) +
        ((Bpol M pol) ^ (s - 1)).mulVec
          (Sum.elim v1 v0 - Sum.elim (valuePol M pol) (valuePol M pol)) := by sorry

end AccelVI.MVC
