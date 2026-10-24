-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
-- name    : AvramDividend.Classical.paymentTimes_min_ofReal_eq_inter_Iio_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:55:09.172895+00:00
-- url     : https://prove2.me/theorems/3634eef8-1dc4-4ba5-9478-4dbce286da9e
-- title:
--   Positive-horizon stopped payment times equal the strict-horizon section, including the initial atom
-- statement:
--   For any extended nonnegative ruin clock σ and strictly positive real T, the payment set at min(σ, ofReal T) equals the original pre-ruin payment set intersected with Iio T. This strengthens the proved horizon-subset helper, handles arbitrary σ including 0 and infinity, retains the initial dividend atom and clarifies strict versus closed endpoint at T, which is essential in taking limits of Stieltjes dividends.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_min_ofReal_eq_inter_Iio_of_pos
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    paymentTimes (min σ (ENNReal.ofReal T)) =
      paymentTimes σ ∩ Set.Iio T := by sorry
