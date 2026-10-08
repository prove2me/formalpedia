-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_representation_2_6
-- name    : ConvexRiskFn.Dual.representation_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:58.065301+00:00
-- url     : https://prove2.me/theorems/00ffcdd7-4b19-43d1-9dcb-d5ab42cdaf32
-- title:
--   (2.5)–(2.6), p. 435 — a proper lsc convex ρ is the supremum of ⟨μ, X⟩ − ρ*(μ) over μ ∈ 𝒜 = dom(ρ*)
-- statement:
--   Let $(\mathcal X,\mathcal Y)$ be a paired system as in §2 and $\rho:\mathcal X\to\overline{\mathbb R}$ proper, lower semicontinuous and convex (A1). With $\rho^*(\mu)=\sup_{X}\{\langle\mu,X\rangle-\rho(X)\}$ and $\mathcal A=\operatorname{dom}\rho^*=\{\mu\in\mathcal Y:\rho^*(\mu)<+\infty\}$,
--   $$\rho(X)=\sup_{\mu\in\mathcal A}\{\langle\mu,X\rangle-\rho^*(\mu)\}\qquad\text{for all }X\in\mathcal X.\qquad(2.6)$$
--
--   This is the dual representation of the paper's §2, the first assertion of Theorem 2.2; restricting the supremum of (2.5) from $\mathcal Y$ to $\mathcal A$ removes the measures that contribute $-\infty$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 435, (2.5) and (2.6)

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- (2.5)–(2.6), p. 435: a proper, lower semicontinuous, convex `ρ` satisfies
`ρ(X) = sup_{μ ∈ 𝒜} {⟨μ, X⟩ − ρ*(μ)}` for all `X`, with `𝒜 = dom(ρ*)`. -/
theorem representation_2_6 {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (ρ : 𝒳 → EReal) (hp : IsProper ρ)
    (hlsc : LowerSemicontinuous ρ) (hcvx : A1 ρ) :
    ∀ X, ρ X = ⨆ μ ∈ dualDom S ρ, ((pair μ (S.toFun X) : ℝ) : EReal) - conj S ρ μ := by sorry
end ConvexRiskFn.Dual
