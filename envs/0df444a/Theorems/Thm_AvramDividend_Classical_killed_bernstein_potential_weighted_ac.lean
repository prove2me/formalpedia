-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_potential_weighted_ac
-- name    : AvramDividend.Classical.killed_bernstein_potential_weighted_ac
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:40:46.355947+00:00
-- url     : https://prove2.me/theorems/ddd470d1-28c9-46f0-9ca6-3f36e2926a2d
-- title:
--   Laplace-derivative convolution proves absolute continuity of weighted Bernstein renewal potential
-- statement:
--   For any killed Bernstein resolvent U with Laplace transform 1/(k+∫(1−e^(−st))κ), and an absolutely continuous positive-half-line kernel κ, show the x-weighted renewal potential xU is absolutely continuous. Differentiate the reciprocal Laplace transform, identify xU with (tκ)*U*U by Laplace uniqueness after finite positive exponential tilting; tκ is AC because κ is AC, hence so is its convolution with U*U. This addresses the genuine positive-height atomlessness obstacle and avoids the incorrect assumption that weak limits of atomless measures are atomless.
-- source:
--   Proved d1bec0b0 convolution Laplace, 4fb183cd positive-MGF uniqueness, pinned hasDerivAt_integral_pow_mul_exp_real, Mathlib Measure.conv_absolutelyContinuous. Child of 8c56d3e5.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_potential_weighted_ac (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (U : Measure ℝ)
    (hUsupp : U (Iio (0 : ℝ)) = 0)
    (hUmass : U Set.univ = ENNReal.ofReal (k⁻¹))
    (hULap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        (ENNReal.ofReal k +
          (∫⁻ t : ℝ,
            ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹)
    (hκac : κ ≪ (volume : Measure ℝ)) :
    (U.withDensity (fun x : ℝ => ENNReal.ofReal x)) ≪
      (volume : Measure ℝ) := by sorry
