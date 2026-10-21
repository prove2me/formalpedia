-- Prove2me | Theorems.Thm_DCPenalty_Penalty_corollary_2_1
-- name    : DCPenalty.Penalty.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:10.998025+00:00
-- url     : https://prove2.me/theorems/16dcdb23-4528-46c2-95d6-b2aa6d24b621
-- title:
--   Corollary 2.1 (PSCQ branch), p. 8 — T_Ω(x̄) = ⋃ C_J(x̄) = ⋃ T_{Y_J(x̄)}(x̄) over J ∈ J(x̄)
-- statement:
--   Let the standing assumptions of problem (1.1) hold, and let $\bar x\in\Omega$ with $\mathcal I_=(\bar x)\neq\emptyset$ be a point at which the PSCQ holds for $\Omega$. Then
--
--   $$
--   \mathcal T_\Omega(\bar x)=\bigcup_{\mathbb J\in\mathcal J(\bar x)}C_{\mathbb J}(\bar x)=\bigcup_{\mathbb J\in\mathcal J(\bar x)}\mathcal T_{Y_{\mathbb J}(\bar x)}(\bar x).
--   $$
--
--   Under the PSCQ the tangent cone of the nonconvex feasible region is a finite union of cones of convex sets, which is what makes B-stationarity checkable piece by piece (Theorem 2.1).
--
--   **Formalization Note** Only the PSCQ branch is stated; the polyhedral/affine/piecewise-affine alternative of the paper is omitted (used only by Theorem 3.1(iv), not formalized).
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 8, Corollary 2.1, PSCQ branch

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

/-- Corollary 2.1, p. 8 (PSCQ branch): if `x̄ ∈ Ω`, `𝓘_=(x̄) ≠ ∅` and the PSCQ holds at `x̄`, then
`𝒯_Ω(x̄) = ⋃_{𝕁 ∈ 𝓙(x̄)} C_𝕁(x̄) = ⋃_{𝕁 ∈ 𝓙(x̄)} 𝒯_{Y_𝕁(x̄)}(x̄)`. -/
theorem corollary_2_1 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    (hpscq : P.PSCQ xbar) :
    tangentConeB P.Ω xbar = ⋃ jj ∈ P.Jtup xbar, P.C jj xbar ∧
      ⋃ jj ∈ P.Jtup xbar, P.C jj xbar = ⋃ jj ∈ P.Jtup xbar, tangentConeB (P.Y jj xbar) xbar := by sorry

end DCPenalty.Penalty
