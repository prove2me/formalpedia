-- Prove2me | Theorems.Thm_DCPenalty_Penalty_proposition_2_1
-- name    : DCPenalty.Penalty.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:09.493982+00:00
-- url     : https://prove2.me/theorems/b44db188-8be4-465c-a9bb-d6c3ec563943
-- title:
--   Proposition 2.1 (under (2.4)), p. 6 — T_{Y_J(x̄)}(x̄) = T_{Ω_J}(x̄) = C_J(x̄)
-- statement:
--   Let the standing assumptions of problem (1.1) hold. Let $\bar x\in\Omega$ with $\mathcal I_=(\bar x)\neq\emptyset$ and $\mathbb J=(j_1,\dots,j_I)\in\mathcal J(\bar x)$. Suppose there is some $\bar d\in\mathcal T_X(\bar x)$ with
--
--   $$
--   \nabla\phi_i(\bar x)^T\bar d+\zeta_i'(\bar x;\bar d)-\nabla\psi_{i,j_i}(\bar x)^T\bar d<0\qquad\forall i\in\mathcal I_=(\bar x). \tag{2.4}
--   $$
--
--   Then
--
--   $$
--   \mathcal T_{Y_{\mathbb J}(\bar x)}(\bar x)=\mathcal T_{\Omega_{\mathbb J}}(\bar x)=C_{\mathbb J}(\bar x).
--   $$
--
--   The tangent cone of the nonconvex piece $\Omega_{\mathbb J}$ thus equals that of its convex inner approximation $Y_{\mathbb J}(\bar x)$ and the linearized cone. The paper omits the proof, referring to Propositions 2 and 3 of Pang, Razaviyayn and Alvarado (2017).
--
--   **Formalization Note** Only the branch under condition (2.4) is stated. The paper's alternative hypothesis ($X$ polyhedral, $\phi_i$ affine and $\zeta_i$ piecewise affine on $X$ for $i\in\mathcal I_=(\bar x)$) is omitted: only Theorem 3.1(iv), which this mission does not formalize, uses it.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 6, Proposition 2.1, (2.4) branch

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open ClarkeGradients.MaxFunctions

/-- Proposition 2.1, p. 6, under condition (2.4): let `x̄ ∈ Ω` with `𝓘_=(x̄) ≠ ∅` and
`𝕁 ∈ 𝓙(x̄)`. If some `d̄ ∈ 𝒯_X(x̄)` satisfies
`∇φ_i(x̄)ᵀd̄ + ζ_i′(x̄; d̄) − ∇ψ_{i,j_i}(x̄)ᵀd̄ < 0` for all `i ∈ 𝓘_=(x̄)`, then
`𝒯_{Y_𝕁(x̄)}(x̄) = 𝒯_{Ω_𝕁}(x̄) = C_𝕁(x̄)`. -/
theorem proposition_2_1 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar)
    (h24 : ∃ d ∈ tangentConeB P.X xbar, ∀ i ∈ P.Ieq xbar,
      ∃ c, HasOneSidedDirDeriv (P.ζ i.succ) xbar d c ∧
        fderiv ℝ (P.φ i.succ) xbar d + c - fderiv ℝ (P.ψ i.succ (jj i)) xbar d < 0) :
    tangentConeB (P.Y jj xbar) xbar = tangentConeB (P.Ωj jj) xbar ∧
      tangentConeB (P.Ωj jj) xbar = P.C jj xbar := by sorry

end DCPenalty.Penalty
