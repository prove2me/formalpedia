-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
-- name    : AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:52:48.776105+00:00
-- url     : https://prove2.me/theorems/5b6aa6af-4b35-488e-9247-2b96c9b4472e
-- title:
--   Original real stopped clock payment support lies in its closed horizon, including instantaneous-ruin atom
-- statement:
--   The original payment selector truncated at any nonnegative deterministic real horizon T is contained in Iic T. At T>0, the existing public strict-endpoint identity identifies it with paymentTimes τ intersect Iio T. At T=0, the existing public zero-clock identity retains precisely the initial time-zero atom. This uniformly covers both boundary cases without assuming stochastic integrability, smoothness or replacing the actual Stieltjes clock.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
    (τ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (min τ (ENNReal.ofReal T)) ⊆ Set.Iic T := by sorry
