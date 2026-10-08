-- Prove2me | Theorems.Thm_CondRiskMap_Repr_dom_conj_subset_probGiven
-- name    : CondRiskMap.Repr.dom_conj_subset_probGiven
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:55.356165+00:00
-- url     : https://prove2.me/theorems/de7bf9e8-e957-489b-84e5-8dc058783022
-- title:
--   Proof of Theorem 1, pp. 5–6 — dom ρ*_ω ⊆ 𝒫_{𝒴₂|ℱ₁}(ω)
-- statement:
--   Let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying the standing conditions (C) and (C′), and let $\rho:\mathcal X_2\to\mathcal X_1$ be a lower semicontinuous conditional risk mapping (axioms (A1)–(A3)). Then for every $\omega\in\Omega$ the effective domain of the conjugate $\rho^*_\omega=\rho^*(\cdot,\omega)$ consists of probability measures that "know" $\mathcal F_1$ at $\omega$:
--   $$
--   \operatorname{dom}\rho^*_\omega=\{\mu\in\mathcal Y_2:\rho^*(\mu,\omega)<+\infty\}\subseteq\mathcal P_{\mathcal Y_2|\mathcal F_1}(\omega),
--   $$
--   that is, every such $\mu$ is a nonnegative measure with $\mu(\Omega)=1$ and $\mu(B)=\mathbb 1_B(\omega)$ for every $B\in\mathcal F_1$.
--
--   This is the step that turns the unconditional Fenchel–Moreau representation of each $\rho_\omega$ into the conditional representation (3.6) of Theorem 1.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, pp. 5–6, proof of Theorem 1 (last paragraph of p. 5 to the first paragraph of p. 6: "It follows that dom ρ*_ω ⊆ 𝒫_{𝒴₂|ℱ₁}(ω).")

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem dom_conj_subset_probGiven {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hlsc : IsLsc S ρ) :
    ∀ ω, envelope S ρ ω ⊆ ProbGiven S ω := by sorry

end CondRiskMap.Repr
