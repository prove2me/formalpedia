-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_original_restricted_real_time_ruin_singleton_null
-- name    : AvramDividend.Classical.avram_bva21_original_restricted_real_time_ruin_singleton_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:48:54.309691+00:00
-- url     : https://prove2.me/theorems/9efe97aa-43dd-4308-bd66-e36fc7928922
-- title:
--   Original real-volume finite horizon assigns zero mass to the ruin boundary time
-- statement:
--   The real finite-horizon integration measure used to express the original K compensator after change of variables is Lebesgue volume restricted to [0,T]. Every singleton, in particular a positive finite ruin boundary time, has zero restricted volume. This removes the sole strict-vs-nonstrict ruin endpoint from the almost-everywhere integral convergence required for 7ccc2a1a.
-- source:
--   Necessary original finite-time ruin boundary null-set atom for a.e. original compensated-grid convergence 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva21_original_restricted_real_time_ruin_singleton_null
    (T r : ℝ) :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Icc 0 T)) ({r} : Set ℝ) = 0 := by sorry
