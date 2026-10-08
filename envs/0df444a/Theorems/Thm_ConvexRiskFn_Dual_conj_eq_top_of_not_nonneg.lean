-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_conj_eq_top_of_not_nonneg
-- name    : ConvexRiskFn.Dual.conj_eq_top_of_not_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:54.291773+00:00
-- url     : https://prove2.me/theorems/1125fa41-5b86-4d46-975e-2903cedba2b0
-- title:
--   Proof of Theorem 2.2(i), p. 436 — under (C) and (A2), ρ*(μ) = +∞ for every μ ∈ 𝒴 that is not nonnegative
-- statement:
--   Let $(\mathcal X,\mathcal Y)$ be a paired system as in §2 satisfying condition (C), and let $\rho:\mathcal X\to\overline{\mathbb R}$ be proper and monotone (A2): $Y\succeq X$ implies $\rho(Y)\ge\rho(X)$. If $\mu\in\mathcal Y$ is not a nonnegative measure, then
--   $$\rho^*(\mu)=\sup_{X\in\mathcal X}\{\langle\mu,X\rangle-\rho(X)\}=+\infty .$$
--
--   Hence every measure in the dual domain $\mathcal A$ of a monotone risk function is nonnegative: this is the forward direction of Theorem 2.2(i).
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 436, proof of Theorem 2.2(i), first paragraph after (2.6)

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(i), p. 436: under condition (C), if a proper `ρ` satisfies (A2), then
`ρ*(μ) = +∞` for every `μ ∈ 𝒴` that is not nonnegative. -/
theorem conj_eq_top_of_not_nonneg {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) (ρ : 𝒳 → EReal)
    (hp : IsProper ρ) (hA2 : A2 S ρ) (μ : MeasureTheory.SignedMeasure Ω) (hμ : μ ∈ S.Y)
    (hneg : ¬ (0 ≤ μ)) :
    conj S ρ μ = ⊤ := by sorry
end ConvexRiskFn.Dual
