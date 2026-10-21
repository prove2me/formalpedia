-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_1_16
-- name    : DCPenalty.Penalty.eq_1_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:40.599421+00:00
-- url     : https://prove2.me/theorems/21310a30-bfe4-4061-9cfb-6fe3b7cbce46
-- title:
--   (1.16), p. 5 — Danskin's formula ψ_i′(x; d) = max_{j ∈ J_i(x)} ∇ψ_{i,j}(x)ᵀd
-- statement:
--   Let the standing assumptions of problem (1.1) hold. Then for every $x\in X$, every $d\in\mathcal T_X(x)$ and every $i\in\{0,1,\dots,I\}$, the one-sided directional derivative of $\psi_i=\max_j\psi_{i,j}$ exists and
--
--   $$
--   \psi_i'(x;d)=\max_{j\in\mathcal J_i(x)}\nabla\psi_{i,j}(x)^Td.
--   $$
--
--   The paper attributes this to Danskin's theorem; it is how directional derivatives of $F$ and of the constraints reduce to those of smooth pieces at the active indices.
--
--   **Formalization Note** The conclusion says that the limit exists and equals the greatest element of $\{\nabla\psi_{i,j}(x)^Td:\ j\in\mathcal J_i(x)\}$ (`IsGreatest` of the image), which also records that the maximum is attained over the nonempty active set.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 5, (1.16)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open ClarkeGradients.MaxFunctions

/-- (1.16), p. 5 (Danskin): `ψ_i′(x; d) = max_{j ∈ 𝓙_i(x)} ∇ψ_{i,j}(x)ᵀd` for all `x ∈ X`,
`d ∈ 𝒯_X(x)` and `i ∈ {0, 1, …, I}`: the one-sided directional derivative exists and equals the
greatest of the values `∇ψ_{i,j}(x)ᵀd` over the active pieces. -/
theorem eq_1_16 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) :
    ∀ x ∈ P.X, ∀ d ∈ tangentConeB P.X x, ∀ i : Fin (m + 1),
      ∃ c, HasOneSidedDirDeriv (P.psi i) x d c ∧
        IsGreatest ((fun j => fderiv ℝ (P.ψ i j) x d) '' (P.Jact i x)) c := by sorry

end DCPenalty.Penalty
