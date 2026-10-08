-- Prove2me | Theorems.Thm_ConvexRiskFn_Dual_dual_cone
-- name    : ConvexRiskFn.Dual.dual_cone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:57.180507+00:00
-- url     : https://prove2.me/theorems/7b861afc-0250-436d-8630-31a8f06a16d9
-- title:
--   §2, p. 434 — under condition (C), 𝒴₊ is the dual cone of 𝒳₊
-- statement:
--   In the paired system $(\mathcal X,\mathcal Y)$ of §2, with $\langle\mu,X\rangle=\int_\Omega X\,d\mu$, assume condition (C): every $\mu\in\mathcal Y$ that is not a nonnegative measure satisfies $\langle\mu,X\rangle<0$ for some $X\in\mathcal X_+$. Then the cone of nonnegative measures in $\mathcal Y$ is the dual of the cone of nonnegative functions in $\mathcal X$:
--   $$\mathcal Y_+=\{\mu\in\mathcal Y:\ \langle\mu,X\rangle\ge 0\ \ \forall X\in\mathcal X_+\}.$$
--
--   This identifies nonnegativity of a measure through the pairing alone, which is how monotonicity (A2) is read off the dual domain in Theorem 2.2(i).
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 434, §2, display after "the cone of nonnegative measures" (consequence of condition (C))

import Mathlib
import Definitions.Def_ConvexRiskFn_Dual_Setting

namespace ConvexRiskFn.Dual

/-- §2, p. 434: under condition (C), the cone `𝒴₊` of nonnegative measures is dual to the cone
`𝒳₊` of nonnegative functions: `𝒴₊ = {μ ∈ 𝒴 : ⟨μ, X⟩ ≥ 0 ∀ X ∈ 𝒳₊}`. -/
theorem dual_cone {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [AddCommGroup 𝒳] [Module ℝ 𝒳]
    [TopologicalSpace 𝒳] [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    (S : PairedSpaces Ω 𝒳) (hC : CondC S) :
    Ypos S = {μ | μ ∈ S.Y ∧ ∀ X ∈ Xpos S, 0 ≤ pair μ (S.toFun X)} := by sorry
end ConvexRiskFn.Dual
