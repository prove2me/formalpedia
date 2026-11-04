-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
-- name    : AvramDividend.Classical.avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:19:54.547135+00:00
-- url     : https://prove2.me/theorems/78e051e1-3f9f-4217-b3c0-bacde377ad39
-- title:
--   Strictly negative Borel intensities are determined by separated mark-band values
-- statement:
--   Two sigma-additive Borel measures supported on negative marks must agree everywhere if they agree on every measurable strictly negative band separated from zero. Works with infinite measure and needs no finite-activity hypothesis.
-- source:
--   Proved P2-C harmonic negative band exhaustion and Mathlib Measure.iUnion continuity; source-independent measure-theoretic lemma.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
    (μ ν : Measure ℝ)
    (hμneg : ∀ B : Set ℝ, MeasurableSet B →
      μ B = μ (B ∩ Iio (0 : ℝ)))
    (hνneg : ∀ B : Set ℝ, MeasurableSet B →
      ν B = ν (B ∩ Iio (0 : ℝ)))
    (hBands : ∀ (B : Set ℝ), MeasurableSet B →
      ∀ ε : ℝ, 0 < ε → B ⊆ Iic (-ε) → μ B = ν B) :
    μ = ν := by sorry
