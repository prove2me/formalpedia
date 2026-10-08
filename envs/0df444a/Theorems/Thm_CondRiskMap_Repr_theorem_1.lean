-- Prove2me | Theorems.Thm_CondRiskMap_Repr_theorem_1
-- name    : CondRiskMap.Repr.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:01.148521+00:00
-- url     : https://prove2.me/theorems/ce8947e1-252c-4cad-acca-82b37e754536
-- title:
--   Theorem 1, p. 5 — dual representation (3.6) of lower semicontinuous conditional risk mappings, and its converse
-- statement:
--   Let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying the standing conditions (C) and (C′).
--
--   1. If $\rho:\mathcal X_2\to\mathcal X_1$ is a lower semicontinuous conditional risk mapping, then for every $\omega\in\Omega$ and $X\in\mathcal X_2$
--   $$
--   \rho_\omega(X)=\sup_{\mu\in\mathcal P_{\mathcal Y_2|\mathcal F_1}(\omega)}\bigl\{\langle\mu,X\rangle-\rho^*(\mu,\omega)\bigr\},\qquad(3.6)
--   $$
--   where $\rho^*$ is the conjugate (3.4) and the supremum is taken in $\overline{\mathbb R}$.
--   2. Conversely, let $\rho:\mathcal X_2\to\mathcal X_1$ be any mapping and $\rho^*:\mathcal Y_2\times\Omega\to\overline{\mathbb R}$ any function such that (3.6) holds for every $\omega$ and $X$. Then $\rho$ is lower semicontinuous and satisfies (A1)–(A3).
--
--   This is the basic duality result for conditional risk mappings: the risk at $\omega$ is a worst case of expected values over probability measures that are consistent with the information $\mathcal F_1$ revealed at $\omega$, penalised by $\rho^*$.
--
--   **Formalization Note** In the converse, $\rho^*$ is an arbitrary function into `EReal`, as in the paper, and not the conjugate. A term with $\rho^*(\mu,\omega)=+\infty$ contributes $-\infty$ to the supremum.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 5, Theorem 1, (3.6)

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) :
    (∀ ρ : 𝒳 → 𝒳, IsCondRiskMapping S ρ → IsLsc S ρ →
      ∀ ω X, ((ρω S ρ ω X : ℝ) : EReal) =
        ⨆ μ ∈ ProbGiven S ω, ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - conj S ρ μ ω) ∧
    (∀ ρ : 𝒳 → 𝒳, MapsToX₁ S ρ → ∀ ρs : 𝒴 → Ω → EReal,
      (∀ ω X, ((ρω S ρ ω X : ℝ) : EReal) =
        ⨆ μ ∈ ProbGiven S ω, ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - ρs μ ω) →
      IsLsc S ρ ∧ A1 S ρ ∧ A2 S ρ ∧ A3 S ρ) := by sorry

end CondRiskMap.Repr
