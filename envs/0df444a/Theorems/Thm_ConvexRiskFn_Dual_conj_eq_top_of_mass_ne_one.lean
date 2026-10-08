-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_conj_eq_top_of_mass_ne_one
-- name    : ConvexRiskFn.Dual.conj_eq_top_of_mass_ne_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:58.088393+00:00
-- url     : https://prove2.me/theorems/5ec87f41-9b69-4be3-abfd-2cfc94da53a0
-- title:
--   Proof of Theorem 2.2(ii), p. 436 — under (A3), ρ*(μ) = +∞ for every μ ∈ 𝒴 with μ(Ω) ≠ 1
-- statement:
--   Let $(\mathcal X,\mathcal Y)$ be a paired system as in §2 in which $\mathcal X$ contains the constant function $\mathbf 1$, and let $\rho:\mathcal X\to\overline{\mathbb R}$ be proper and translation equivariant (A3): $\rho(X+a)=\rho(X)+a$ for all $a\in\mathbb R$. If $\mu\in\mathcal Y$ has total mass $\mu(\Omega)\ne 1$, then
--   $$\rho^*(\mu)=+\infty .$$
--
--   Hence every measure in the dual domain of a translation-equivariant risk function has total mass one: the forward direction of Theorem 2.2(ii).
--
--   **Formalization Note** The constant function $a$ is $a\cdot\mathbf 1$ for an element $\mathbf 1\in\mathcal X$ assumed equal to the constant function $1$; (A3) presupposes that constants lie in $\mathcal X$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 436, proof of Theorem 2.2(ii)

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- Proof of Theorem 2.2(ii), p. 436: if `𝒳` contains the constant function `1` and a proper `ρ`
satisfies (A3), then `ρ*(μ) = +∞` for every `μ ∈ 𝒴` with `μ(Ω) ≠ 1`. -/
theorem conj_eq_top_of_mass_ne_one {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (one : 𝒳)
    (hone : S.toFun one = fun _ => 1) (ρ : 𝒳 → EReal) (hp : IsProper ρ) (hA3 : A3 one ρ)
    (μ : MeasureTheory.SignedMeasure Ω) (hμ : μ ∈ S.Y) (hmass : μ Set.univ ≠ 1) :
    conj S ρ μ = ⊤ := by sorry
end ConvexRiskFn.Dual
