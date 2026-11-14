-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass
-- name    : AvramDividend.Classical.avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T18:02:33.663285+00:00
-- url     : https://prove2.me/theorems/dfe5db81-0c95-4f46-a570-25c950dbbde2
-- title:
--   Source predictable true physical time measure on nonnegative [0,T] has exactly real mass T after map to nonnegative time
-- statement:
--   For the exact source physical predictable time measure obtained by pushing ordinary Lebesgue volume restricted to real [0,T] through Real.toNNReal, prove its real total mass is exactly T for any nonnegative physical horizon. This is the non-approximated time-mass identity needed to bound original V_n negative mark compensator in topcap BVB72, with no replacement time clock.
-- source:
--   Pinned Measure.map_apply measurable_real_toNNReal and Real.volume_Icc, hT nonneg.

import Mathlib
open Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass
    (T : ℝ) (hT : 0 ≤ T) :
    ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal).real Set.univ) = T := by sorry
