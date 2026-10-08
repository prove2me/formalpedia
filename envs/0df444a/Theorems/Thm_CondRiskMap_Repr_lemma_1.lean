-- Prove2me | Theorems.Thm_CondRiskMap_Repr_lemma_1
-- name    : CondRiskMap.Repr.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:55.196171+00:00
-- url     : https://prove2.me/theorems/9e8fb4ed-adc1-4d46-9b83-b7b091a8dd11
-- title:
--   Lemma 1, p. 11 — for separable 𝒳₂, ρ is the supremum of countably many weakly* ℱ₁-measurable selections of 𝒜 (4.7)
-- statement:
--   Let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying (C) and (C′), with $\mathcal X_2$ **separable** (it has a countable dense subset). Let $\rho$ be a positively homogeneous, lower semicontinuous conditional risk mapping, so that the representation (3.8) holds with the risk envelope $\mathcal A(\omega)$. Then there is a sequence $\mu^i$, $i\in\mathbb N$, of weakly\* $\mathcal F_1$-measurable selections of $\mathcal A$ (that is, $\mu^i_\omega\in\mathcal A(\omega)$ for every $\omega$, and $\omega\mapsto\langle\mu^i_\omega,X\rangle$ is $\mathcal F_1$-measurable for every $X\in\mathcal X_2$) such that
--   $$
--   [\rho(X)](\omega)=\sup_{i\in\mathbb N}\langle\mu^i_\omega,X\rangle\qquad(4.7)
--   $$
--   for all $X\in\mathcal X_2$ and $\omega\in\Omega$.
--
--   The lemma replaces the possibly uncountable envelope by countably many measurable selections; combined with fixed points of the operators $\mathbb Q_{\mu^i}$ it yields the conditional expectation representation of Theorem 2.
--
--   **Formalization Note** "The representation (3.8) holds" is not a separate hypothesis: under the stated hypotheses it is the content of the milestone `envelope_representation_3_8`. The supremum is stated with `IsLUB`.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 11, Lemma 1, (4.7)

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    [TopologicalSpace.SeparableSpace 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ) :
    ∃ κ : ℕ → Ω → 𝒴, (∀ i, IsSelection S ρ (κ i)) ∧
      ∀ X ω, IsLUB (Set.range fun i => pair (S.toMeasure (κ i ω)) (S.toFun X)) (ρω S ρ ω X) := by sorry

end CondRiskMap.Repr
