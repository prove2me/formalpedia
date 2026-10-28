-- Prove2me | Theorems.Thm_FiniteEnergyPlane_abs_integral_bilin_sub_le_of_eq
-- name    : FiniteEnergyPlane.abs_integral_bilin_sub_le_of_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-24T22:59:47.996288+00:00
-- url     : https://prove2.me/theorems/ba358209-c0b6-4474-88be-7d12f22f35c8
-- title:
--   Boundary term of a closed curve bounded by its energy
-- statement:
--   Let $F$ be a real Banach space, $\sigma:F\times F\to\mathbb{R}$ a continuous bilinear form, $a\le b$, and $\gamma:\mathbb{R}\to F$ with derivative $\gamma'(t)$ at every $t\in[a,b]$, where $\gamma'$ is continuous on $[a,b]$ and $\gamma(a)=\gamma(b)$. Then for every $q\in F$,
--   $$\left|\int_a^b\sigma\big(\gamma(t)-q,\ \gamma'(t)\big)\,dt\right|\le\|\sigma\|\,(b-a)\int_a^b\|\gamma'(t)\|^2\,dt .$$
--
--   For a closed curve, the boundary term $\int\sigma(\gamma-q,\gamma')$ is controlled by the energy of the curve, uniformly in the base point $q$. This is the boundary estimate used for energy decay of pseudoholomorphic maps on small discs.
--
--   **Formalization Note** `σ : F →L[ℝ] F →L[ℝ] ℝ` with operator norm `‖σ‖`. Differentiability is required as `HasDerivAt γ (γ' t) t` at each `t ∈ Icc a b`.
-- source:
--   Standard

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Bound for the boundary term of a closed curve. Let `σ` be a continuous bilinear form on a Banach
space `F`, let `γ` be `C¹` on `[a, b]` with derivative `γ'` and `γ a = γ b`, and let `q ∈ F`. Then
`|∫ₐᵇ σ(γ - q, γ')| ≤ ‖σ‖ (b - a) ∫ₐᵇ ‖γ'‖²`. -/
theorem abs_integral_bilin_sub_le_of_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) {γ γ' : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hper : γ a = γ b) (q : F) :
    |∫ t in a..b, σ (γ t - q) (γ' t)| ≤ ‖σ‖ * (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
