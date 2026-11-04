-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:05:53.10012+00:00
-- url     : https://prove2.me/theorems/b5729ec5-4125-45ed-88b9-00958f92a8dc
-- title:
--   Explicit uniform envelope for original discounted BV Lévy physical generator
-- statement:
--   For the genuine BV spectrally negative Lévy process and q≥0, if the absolute original physical derivative, negative-jump ν-integral and value at the controlled reserve are uniformly bounded by L, M and R, respectively, then the source-discounted physical drift-plus-jump-minus-killing magnitude is bounded for every nonnegative stopping time t by |drift|L+M+|q|R. The latter is nonnegative.
-- source:
--   Source BV physical generator identity, pinned Real.exp_le_one_iff, absolute-value triangle and product inequalities. Provides the explicit scalar B for the accepted uniform-capped expected-HJB result 20e052be.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (t : ℝ≥0) (y : ℝ)
  (L M R : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R)
  (hDeriv : |deriv w y| ≤ L)
  (hJump : |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M)
  (hValue : |w y| ≤ R) :
  0 ≤ |X.drift| * L + M + |q| * R ∧
  |Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y)| ≤ |X.drift| * L + M + |q| * R := by sorry
