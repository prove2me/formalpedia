-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_2_1
-- name    : DCPenalty.Penalty.eq_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:59.314976+00:00
-- url     : https://prove2.me/theorems/ea0a82b2-809c-44fa-8337-57a1089b3de3
-- title:
--   (2.1), p. 6 — T_Ω(x̄) is the union of the tangent cones T_{Ω_J}(x̄) over J ∈ J(x̄)
-- statement:
--   Let the standing assumptions of problem (1.1) hold. Then for every $\bar x\in\Omega$,
--
--   $$
--   \mathcal T_\Omega(\bar x)=\bigcup_{\mathbb J\in\mathcal J(\bar x)}\mathcal T_{\Omega_{\mathbb J}}(\bar x).
--   $$
--
--   The nonconvex feasible region is, near $\bar x$, the finite union of the sets $\Omega_{\mathbb J}$ with $\mathbb J$ active at $\bar x$; this identity reduces the tangent cone of $\Omega$ to those of the pieces, which Proposition 2.1 characterizes.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 6, (2.1)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

/-- (2.1), p. 6: `𝒯_Ω(x̄) = ⋃_{𝕁 ∈ 𝓙(x̄)} 𝒯_{Ω_𝕁}(x̄)` for every `x̄ ∈ Ω`. -/
theorem eq_2_1 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) :
    ∀ xbar ∈ P.Ω, tangentConeB P.Ω xbar = ⋃ jj ∈ P.Jtup xbar, tangentConeB (P.Ωj jj) xbar := by sorry

end DCPenalty.Penalty
