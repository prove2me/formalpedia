-- Prove2me | Theorems.Thm_CondRiskMap_Repr_envelope_representation_3_8
-- name    : CondRiskMap.Repr.envelope_representation_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:36.715212+00:00
-- url     : https://prove2.me/theorems/88f2a7bd-a21b-4754-bd42-f975081ee471
-- title:
--   (3.8), p. 6 — ρ*(·, ω) is the indicator of a closed convex 𝒜(ω) ⊂ 𝒫_{𝒴₂|ℱ₁}(ω) and ρ_ω(X) = sup_{μ∈𝒜(ω)} ⟨μ, X⟩
-- statement:
--   Let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying (C) and (C′), and let $\rho$ be a positively homogeneous, lower semicontinuous conditional risk mapping. Write $\mathcal A(\omega)=\{\mu\in\mathcal Y_2:\rho^*(\mu,\omega)<+\infty\}$. Then for every $\omega\in\Omega$:
--   1. $\rho^*(\cdot,\omega)$ is the indicator function of $\mathcal A(\omega)$: it equals $0$ on $\mathcal A(\omega)$ and $+\infty$ off it;
--   2. $\mathcal A(\omega)$ is closed (in the topology of $\mathcal Y_2$) and convex;
--   3. $\mathcal A(\omega)\subseteq\mathcal P_{\mathcal Y_2|\mathcal F_1}(\omega)$;
--   4. for every $X\in\mathcal X_2$,
--   $$
--   \rho_\omega(X)=\sup_{\mu\in\mathcal A(\omega)}\langle\mu,X\rangle,\qquad(3.8)
--   $$
--   the supremum being the least upper bound of the real numbers $\langle\mu,X\rangle$, $\mu\in\mathcal A(\omega)$.
--
--   The multifunction $\omega\mapsto\mathcal A(\omega)$ is the conditional **risk envelope**; (3.8) is the form of the representation on which §4 builds.
--
--   **Formalization Note** The supremum in (3.8) is stated with `IsLUB` over the image of $\mathcal A(\omega)$; this also asserts that $\mathcal A(\omega)$ is nonempty and the set is bounded above.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 6, paragraph after Proposition 1, (3.8)

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem envelope_representation_3_8 {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ) :
    ∀ ω, (∀ μ ∈ envelope S ρ ω, conj S ρ μ ω = 0) ∧ (∀ μ ∉ envelope S ρ ω, conj S ρ μ ω = ⊤) ∧
      IsClosed (envelope S ρ ω) ∧ Convex ℝ (envelope S ρ ω) ∧
      envelope S ρ ω ⊆ ProbGiven S ω ∧
      ∀ X, IsLUB ((fun μ => pair (S.toMeasure μ) (S.toFun X)) '' envelope S ρ ω) (ρω S ρ ω X) := by sorry

end CondRiskMap.Repr
