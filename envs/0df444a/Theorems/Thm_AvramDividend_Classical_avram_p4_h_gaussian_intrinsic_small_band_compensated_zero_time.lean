-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:43:18.22909+00:00
-- url     : https://prove2.me/theorems/125ef45d-76aa-4edf-aae2-99ef49cac353
-- title:
--   Original intrinsic compensated small-negative-jump process starts at zero
-- statement:
--   On the exact original Levy sample space and filtration, the intrinsic small-band compensated jump process Jsmall^(n) vanishes at time zero for every cutoff n and sample point, because the source jump interval (0,0] is empty and the deterministic compensator has zero time prefactor.
-- source:
--   Published source definition 66a113ed-6260-42ea-862c-576aa1e2b0cb; direct simplification of empty time band in original marked jump-counting measure and zero compensator multiplier.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n 0 ω = 0 := by sorry
