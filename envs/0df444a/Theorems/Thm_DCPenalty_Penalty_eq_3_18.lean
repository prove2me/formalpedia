-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_3_18
-- name    : DCPenalty.Penalty.eq_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:34.678543+00:00
-- url     : https://prove2.me/theorems/f00191cf-f3d6-453e-bb0b-70d632fdf2f0
-- title:
--   (3.18), p. 11 — under the PSCQ, some x̂ ∈ Y_J(x̄) strictly satisfies the active linearized constraints
-- statement:
--   Let the standing assumptions of problem (1.1) hold, and let $\bar x\in\Omega$ with $\mathcal I_=(\bar x)\neq\emptyset$ be a point at which the PSCQ holds. Then for every $\mathbb J=(j_1,\dots,j_I)\in\mathcal J(\bar x)$ there exists some $\hat x\in Y_{\mathbb J}(\bar x)$ such that
--
--   $$
--   \phi_i(\hat x)+\zeta_i(\hat x)-\ell_{\psi_{i,j_i}}(\hat x;\bar x)<0\qquad\forall i\in\mathcal I_=(\bar x).
--   $$
--
--   In the paper this is the first step of the proof of Theorem 3.1(iii), at $\bar x=x^\infty$; it turns the PSCQ into a Slater point of the convex set $Y_{\mathbb J}(\bar x)$. The statement involves no algorithm and is stated for a general $\bar x$.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 11, proof of Theorem 3.1(iii), (3.18)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

/-- (3.18), p. 11: if `x̄ ∈ Ω`, `𝓘_=(x̄) ≠ ∅` and the PSCQ holds at `x̄`, then for every
`𝕁 ∈ 𝓙(x̄)` some `x̂ ∈ Y_𝕁(x̄)` satisfies
`φ_i(x̂) + ζ_i(x̂) − ℓ_{ψ_{i,j_i}}(x̂; x̄) < 0` for all `i ∈ 𝓘_=(x̄)`. -/
theorem eq_3_18 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    (hpscq : P.PSCQ xbar) :
    ∀ jj ∈ P.Jtup xbar, ∃ xhat ∈ P.Y jj xbar, ∀ i ∈ P.Ieq xbar,
      P.φ i.succ xhat + P.ζ i.succ xhat - lin (P.ψ i.succ (jj i)) xbar xhat < 0 := by sorry

end DCPenalty.Penalty
