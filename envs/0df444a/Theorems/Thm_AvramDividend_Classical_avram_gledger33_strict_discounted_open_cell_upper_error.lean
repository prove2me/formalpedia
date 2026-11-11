-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger33_strict_discounted_open_cell_upper_error
-- name    : AvramDividend.Classical.avram_gledger33_strict_discounted_open_cell_upper_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:34:42.287073+00:00
-- url     : https://prove2.me/theorems/eb1b02a8-9209-4a88-90bd-2adc0b277c1c
-- title:
--   Open crossing-cell discounted original Stieltjes mass bound without terminal atom
-- statement:
--   For any measure on real time, nonnegative discount and times 0 ≤ a ≤ b, the discounted mass on the strictly open interval (a,b) is bounded by [exp(-qb)+q(b-a)] times the open-interval mass. Derive from the Proved right-closed interval theorem by restricting the original measure to times strictly below b. This retains the correct terminal prepayment convention of the original dividend ledger.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger33_strict_discounted_open_cell_upper_error (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : (∫⁻ s in Ioo a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤ ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioo a b) := by sorry
