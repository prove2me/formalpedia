-- Prove2me | Theorems.Thm_CondRiskMap_Repr_exists_fixedPoint_of_K
-- name    : CondRiskMap.Repr.exists_fixedPoint_of_K
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:03.680909+00:00
-- url     : https://prove2.me/theorems/9b9aafeb-fdca-4df5-8de5-99c905866aeb
-- title:
--   §4, p. 10 — under (K), ℚ_μ has a fixed point ν̄ ∈ 𝒫_{𝒴₂} (Kakutani)
-- statement:
--   Let $\Omega$ be nonempty, let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying (C) and (C′), and let $\rho$ be a positively homogeneous, lower semicontinuous conditional risk mapping with risk envelope $\mathcal A(\omega)$. Assume (K): the set $\mathcal P_{\mathcal Y_2}$ of probability measures in $\mathcal Y_2$ is compact and, for every weakly\* $\mathcal F_1$-measurable selection $\mu$ of $\mathcal A$, the operator
--   $$
--   [\mathbb Q_\mu(\nu)](A)=\int_\Omega\mu_\omega(A)\,d\nu(\omega),\qquad A\in\mathcal F_2,
--   $$
--   maps $\mathcal P_{\mathcal Y_2}$ into itself and has a closed graph on $\mathcal P_{\mathcal Y_2}$. Then for every weakly\* $\mathcal F_1$-measurable selection $\mu$ of $\mathcal A$ there is $\bar\nu\in\mathcal P_{\mathcal Y_2}$ with
--   $$
--   \int_\Omega\mu_\omega(A)\,d\bar\nu(\omega)=\bar\nu(A)\quad\text{for every }A\in\mathcal F_2.\qquad(4.5)
--   $$
--
--   The fixed point $\bar\nu$ is the probability measure whose conditional probability given $\mathcal F_1$ is the selection $\mu$ (Proposition 3).
--
--   **Formalization Note** $\Omega$ is assumed nonempty: for $\Omega=\emptyset$ all hypotheses hold vacuously while $\mathcal P_{\mathcal Y_2}=\emptyset$.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 10, §4, paragraph after assumption (K): "By Kakutani's Theorem we have that, under the above assumption (K), the operator ℚ_μ has a fixed point ν̄ ∈ 𝒫_{𝒴₂}."

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem exists_fixedPoint_of_K {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴] [Nonempty Ω]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (hK : CondK S ρ) :
    ∀ κ : Ω → 𝒴, IsSelection S ρ κ → ∃ ν ∈ Prob S, IsFixedPoint S κ ν := by sorry

end CondRiskMap.Repr
