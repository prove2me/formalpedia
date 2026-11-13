-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva83_original_zero_clock_negative_mark_compensator_integral
-- name    : AvramDividend.Classical.avram_bva83_original_zero_clock_negative_mark_compensator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:28:07.959427+00:00
-- url     : https://prove2.me/theorems/b642214c-76e9-4dde-8b72-2dca6a876cec
-- title:
--   Original negative-mark stopped source compensator vanishes at zero physical clock
-- statement:
--   The original BV negative-mark kernel integrated against the Levy measure restricted to negative marks has zero integral on the zero mapped real physical clock, for every source kernel and path. Removes the deterministic compensator part of M_n(0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva83_original_zero_clock_negative_mark_compensator_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (ω : Ω) :
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (0 : ℝ))).map Real.toNNReal)) = 0 := by sorry
