-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_eq_truncated_union_terminal
-- name    : AvramDividend.Classical.paymentTimes_closed_horizon_eq_truncated_union_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:14:57.863761+00:00
-- url     : https://prove2.me/theorems/6243111f-991d-4cd6-b99b-5030b5fe97d8
-- title:
--   Closed dividend horizon equals strict stopped horizon plus the terminal payment atom
-- statement:
--   For any nonnegative deterministic time horizon T, the payment times up to and including T equal the payment times of the stopped clock min(σ,ofReal T), together with the possible payment atom at T. At T=0 the initial dividend atom is correctly retained. This is the exact endpoint decomposition required to reconcile the strict stopped-clock convention with the Iic T region used in the BV/UV HJB verification inequalities.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_closed_horizon_eq_truncated_union_terminal (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Set.Iic T =
      paymentTimes (min σ (ENNReal.ofReal T)) ∪
        (paymentTimes σ ∩ ({T} : Set ℝ)) := by sorry
