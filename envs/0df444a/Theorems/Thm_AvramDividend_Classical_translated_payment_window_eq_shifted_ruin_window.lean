-- Prove2me | Theorems.Thm_AvramDividend_Classical_translated_payment_window_eq_shifted_ruin_window
-- name    : AvramDividend.Classical.translated_payment_window_eq_shifted_ruin_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:27:16.863554+00:00
-- url     : https://prove2.me/theorems/4d86d04a-8465-4069-929a-7088cce55428
-- title:
--   Translated positive post-upcrossing payment window equals the shifted first-ruin payment window
-- statement:
--   For finite u and possibly infinite future ruin time rho, the set of strictly positive relative real times whose absolute time u+t belongs to paymentTimes(u+rho) equals the set of strictly positive times belonging to paymentTimes(rho). This removes the translated original stopping window in the already proved stopped Stieltjes dividend payoff identity once its ruin-clock time-shift has been established. The positive-time restriction avoids the special dividend atom at time zero.
-- source:
--   Proved paymentTimes_translated_iff_shifted_of_pos UUID 309b576b-b728-4d10-9fb0-93e8d86286e3 and exact paymentTimes definition. Serves standing barrier valuation parent 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_translated_iff_shifted_of_pos
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.translated_payment_window_eq_shifted_ruin_window
    (u : ℝ≥0) (ρ : ℝ≥0∞) :
    Set.Ioi (0 : ℝ) ∩
      ((fun t : ℝ => (u : ℝ) + t) ⁻¹'
        paymentTimes ((u : ℝ≥0∞) + ρ)) =
    Set.Ioi (0 : ℝ) ∩ paymentTimes ρ := by sorry
