-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
-- name    : AvramDividend.Classical.paymentTimes_terminal_active_lintegral_eq_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:57:25.458867+00:00
-- url     : https://prove2.me/theorems/c58a4a4c-90ac-4fcb-901f-6e1e60d6d727
-- title:
--   Terminal Stieltjes dividend reward equals its atom at an active payment horizon
-- statement:
--   Whenever a real time T belongs to the active pre-ruin dividend payment-time set, the nonnegative Stieltjes integral over its intersection with the singleton {T} is precisely the integrand at T multiplied by the Stieltjes measure mass at T. This exact identity includes the time-zero atom and makes no atomicity assumption on the full dividend process.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_terminal_active_lintegral_eq_atom
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (σ : ℝ≥0∞) (T : ℝ) (hactive : T ∈ paymentTimes σ) :
    (∫⁻ t in paymentTimes σ ∩ ({T} : Set ℝ), f t ∂μ) =
      f T * μ {T} := by sorry
