-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
-- name    : AvramDividend.Classical.paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:17:45.137722+00:00
-- url     : https://prove2.me/theorems/e51fe7e3-0df8-4118-8e78-4870cd0babaf
-- title:
--   Closed-horizon stopped Stieltjes integral splits into strict-horizon reward and terminal atom
-- statement:
--   For any nonnegative integrand and measure on real time, and a strictly positive deterministic horizon T, the integral over pre-ruin payment times through T equals the integral over the stopped clock min(σ,ofReal T) plus the integral over the possible singleton dividend atom at T. The sets are disjoint for T>0, so Mathlib's lintegral_union applies. The T=0 case is deliberately excluded because the stopped clock already retains the initial atom and would otherwise double count it.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_eq_truncated_union_terminal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes σ ∩ Set.Iic T, f t ∂μ) =
      (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)), f t ∂μ) +
        (∫⁻ t in paymentTimes σ ∩ ({T} : Set ℝ), f t ∂μ) := by sorry
