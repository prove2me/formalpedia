-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
-- name    : AvramDividend.Classical.avram_mix_fin14_original_negative_band_shift_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:09:24.657692+00:00
-- url     : https://prove2.me/theorems/238b5785-2c2a-46b2-b08e-e7b4b9ab0e87
-- title:
--   Original negative-band signed jump integral equals its actual shifted-increment-path integral
-- statement:
--   At any deterministic original time shift and horizon, the real signed negative-band jump integral of the original Levy source over the future half-open window equals the integral of the exact shifted-increment path over the relative window. Works for arbitrary negative Borel bands even if individual real integrals are not absolutely integrable, using the pinned signed integral to lintegral convention and the Proved exact all-Borel weighted shift transport 3bf3911b. Needed to express original same-space Gaussian finite-cutoff residual future increments as Borel functionals of independent source increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin14_original_negative_band_shift_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : ∀ z ∈ B, z ≤ 0) :
    (∫ p in (Ioc (0 : ℝ≥0) T ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
