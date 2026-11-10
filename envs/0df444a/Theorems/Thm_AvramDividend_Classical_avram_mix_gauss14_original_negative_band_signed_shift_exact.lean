-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_negative_band_signed_shift_exact
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_negative_band_signed_shift_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:18:29.032845+00:00
-- url     : https://prove2.me/theorems/613d1237-6e63-40c6-9853-710a3c6b7aea
-- title:
--   Same-space signed negative-jump integral is exactly shift-covariant on any deterministic future interval
-- statement:
--   For the original process X, its actual increment path Y(u)=X(s+u)-X(s), and any nonpositive Borel mark band B, identify the original signed real jump mass on (s,s+T] exactly with the shifted-path mass on (0,T]. This uses the source-exact arbitrary Borel weighted positive mass transport and the generic signed real negative-mark window bridge. It is required for original Gaussian residual increments as a function of the genuinely shifted original path and subsequent filtration independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_negative_band_signed_shift_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    let Y := fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
        (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
    let ν : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂ν) =
      (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) := by sorry
