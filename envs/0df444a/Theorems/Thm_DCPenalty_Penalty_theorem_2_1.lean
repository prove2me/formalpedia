-- Prove2me | Theorems.Thm_DCPenalty_Penalty_theorem_2_1
-- name    : DCPenalty.Penalty.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:19.468779+00:00
-- url     : https://prove2.me/theorems/abff7357-8e6e-4078-8df8-592973af25fc
-- title:
--   Theorem 2.1 (PSCQ branch), p. 8 — x̄ is B-stationary for (1.1) iff F′(x̄; d) ≥ 0 on every T_{Y_J(x̄)}(x̄), J ∈ J(x̄)
-- statement:
--   Let the standing assumptions of problem (1.1) hold, and let $\bar x\in\Omega$ with $\mathcal I_=(\bar x)\neq\emptyset$ be a point at which the PSCQ holds for $\Omega$. Then $\bar x$ is a B-stationary point of problem (1.1) if and only if
--
--   $$
--   F'(\bar x;d)\ge 0\qquad\text{for all } d\in\mathcal T_{Y_{\mathbb J}(\bar x)}(\bar x)\text{ and all }\mathbb J\in\mathcal J(\bar x).
--   $$
--
--   It is the last step of the proof of Theorem 3.1(iii): there, (3.26) yields the right-hand side.
--
--   **Formalization Note** "$F'(\bar x;d)\ge 0$" means that the one-sided directional derivative exists and is nonnegative, as in the definition of B-stationarity. Only the PSCQ branch is stated; the polyhedral alternative of the paper is omitted (used only by Theorem 3.1(iv)).
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 8, Theorem 2.1, PSCQ branch

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open ClarkeGradients.MaxFunctions

/-- Theorem 2.1, p. 8 (PSCQ branch): if `x̄ ∈ Ω`, `𝓘_=(x̄) ≠ ∅` and the PSCQ holds at `x̄`, then
`x̄` is a B-stationary point of (1.1) iff `F′(x̄; d) ≥ 0` (the directional derivative exists and
is nonnegative) for all `d ∈ 𝒯_{Y_𝕁(x̄)}(x̄)` and `𝕁 ∈ 𝓙(x̄)`. -/
theorem theorem_2_1 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    (hpscq : P.PSCQ xbar) :
    P.IsBStationary xbar ↔
      ∀ jj ∈ P.Jtup xbar, ∀ d ∈ tangentConeB (P.Y jj xbar) xbar,
        ∃ c, HasOneSidedDirDeriv P.F xbar d c ∧ 0 ≤ c := by sorry

end DCPenalty.Penalty
