-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_all_negative_rate_from_dense_cutoff_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_all_negative_rate_from_dense_cutoff_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:58.437457+00:00
-- url     : https://prove2.me/theorems/999fd8f5-240d-451d-875c-d3ab41262efd
-- title:
--   All negative Borel original Lévy rate from countably many dense harmonic cutoff tests
-- statement:
--   A single dense threshold family and countably many harmonic cutoffs suffice to identify the original process expected intrinsic negative Borel marked-jump rate on every strictly negative mark set, assuming the exact source ν rate only for these elementary tests.
-- source:
--   Composition of Proved P2-C original separated dense-test rate f5b475db, harmonic mark exhaustion 679340e8, and monotone-band rate 42393902. This theorem makes the remaining original analytic test obligation countable, not assumed unconditionally.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_all_negative_rate_from_dense_cutoff_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ))
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ (n : ℕ) (a : ℝ), a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-(1 / ((n : ℝ) + 1))))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-(1 / ((n : ℝ) + 1)))))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
