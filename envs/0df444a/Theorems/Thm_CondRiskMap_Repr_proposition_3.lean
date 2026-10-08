-- Prove2me | Theorems.Thm_CondRiskMap_Repr_proposition_3
-- name    : CondRiskMap.Repr.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:03.513747+00:00
-- url     : https://prove2.me/theorems/5e2cc5c2-aa8d-49c4-b91f-6f3bf96bc0c1
-- title:
--   Proposition 3, p. 9 — a fixed point ν̄ of ℚ_μ makes μ(·) the conditional probability of ν̄ given ℱ₁
-- statement:
--   Let $\mathcal X_2,\mathcal Y_2$ be paired locally convex spaces over $\mathcal F_1\subset\mathcal F_2$ satisfying (C) and (C′), and assume $\mathcal X_2$ contains the indicator $\mathbb 1_A$ of every $A\in\mathcal F_2$. Let $\rho$ be a positively homogeneous, lower semicontinuous conditional risk mapping with risk envelope $\mathcal A(\omega)$, let $\mu$ be a weakly\* $\mathcal F_1$-measurable selection of $\mathcal A$, and let $\bar\nu\in\mathcal P_{\mathcal Y_2}$ be a fixed point of $\mathbb Q_\mu$, i.e. $\int_\Omega\mu_\omega(A)\,d\bar\nu(\omega)=\bar\nu(A)$ for all $A\in\mathcal F_2$. Then $\mu(\cdot)$ is the conditional probability of $\bar\nu$ with respect to $\mathcal F_1$: for every $A\in\mathcal F_2$ the function $\omega\mapsto\mu_\omega(A)$ is $\mathcal F_1$-measurable, and
--   $$
--   \int_S\mu_\omega(A)\,d\bar\nu(\omega)=\bar\nu(A\cap S)\quad\text{for all }S\in\mathcal F_1,\ A\in\mathcal F_2.\qquad(4.6)
--   $$
--
--   Thus each measurable selection of the risk envelope is a regular conditional probability of some probability measure, which is how $\langle\mu_\omega,X\rangle$ becomes a conditional expectation.
--
--   **Formalization Note** The hypothesis that $\mathcal X_2$ contains all indicators $\mathbb 1_A$, $A\in\mathcal F_2$ (the paper's example making (C) hold, p. 4), is added: the proof derives the $\mathcal F_1$-measurability of $\omega\mapsto\mu_\omega(A)=\langle\mu_\omega,\mathbb 1_A\rangle$ from weak\* measurability, which needs $\mathbb 1_A\in\mathcal X_2$; without it the integral in (4.4) could be of a non-measurable function.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 9, Proposition 3 (proof p. 10, (4.6))

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr

theorem proposition_3 {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) (hI : HasIndicators S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ)
    (κ : Ω → 𝒴) (hκ : IsSelection S ρ κ) (ν : 𝒴) (hν : ν ∈ Prob S)
    (hfix : IsFixedPoint S κ ν) :
    IsCondProb S ν κ := by sorry

end CondRiskMap.Repr
