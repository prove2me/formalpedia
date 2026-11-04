-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_negative_rate_from_rational_harmonic_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_negative_rate_from_rational_harmonic_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:00:55.06808+00:00
-- url     : https://prove2.me/theorems/40e9c4f2-7964-4996-93e9-fe152baa9e5d
-- title:
--   Rational-harmonic countable source test family identifies every strictly negative Borel jump rate
-- statement:
--   For the actual Lévy process, knowledge of the source expected marked jump ν rate on the explicitly countable family of rational lower half-lines truncated by harmonic negative cutoffs suffices to identify the rate on any strictly negative Borel mark set. The countable test rates are explicit hypotheses; no assumed compensator or generic replacement law.
-- source:
--   Directly applies the Proved P2-C original separated dense threshold theorem, harmonic negative band exhaustion, and the Proved monotone-band rate theorem. Rat.denseRange_cast supplies the concrete countable dense family. No unproved helper import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_negative_rate_from_rational_harmonic_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ))
    (hTests : ∀ (n : ℕ) (q : ℚ),
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic (q : ℝ) ∩ Iic (-(1 / ((n : ℝ) + 1))))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ) ∩ Iic (-(1 / ((n : ℝ) + 1)))))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
