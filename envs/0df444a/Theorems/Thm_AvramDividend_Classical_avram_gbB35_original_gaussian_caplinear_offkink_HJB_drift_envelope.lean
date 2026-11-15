-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
-- name    : AvramDividend.Classical.avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:46:38.603219+00:00
-- url     : https://prove2.me/theorems/12584a8e-4eb0-4674-b895-276e678d0417
-- title:
--   Original pure-Gaussian cap-linear HJB drift bound off the interior clipping kink
-- statement:
--   For the original pure-Gaussian Levy generator, an interior cap-linear value extension inherits the HJB nonpositive discounted drift below its clipping level and has discounted drift at most the positive part of the source drift above it. The sole excluded point is the interior clipping kink, whose contribution must be handled by occupation/local time with the nonpositive derivative jump.
-- source:
--   Uses B32 upper affine generator, B34 lower local generator, and Proved gfinite59 affine discounted drift estimate. Explicitly excludes y=b; no unproved C2-at-cap assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
import Theorems.Thm_AvramDividend_Classical_avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (y : ℝ) (hy : 0 < y) (hne : y ≠ b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.generator V y - q * V y ≤
      if b < y then max X.c 0 else 0 := by sorry
