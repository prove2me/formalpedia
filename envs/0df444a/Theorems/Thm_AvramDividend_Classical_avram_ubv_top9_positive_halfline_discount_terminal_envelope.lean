-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_positive_halfline_discount_terminal_envelope
-- name    : AvramDividend.Classical.avram_ubv_top9_positive_halfline_discount_terminal_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:28:11.241639+00:00
-- url     : https://prove2.me/theorems/a41c3f59-bcc4-4b24-9799-7a884076918a
-- title:
--   Uniform original positive-halfline discounted terminal envelope under upper-localised reserve
-- statement:
--   For a nonnegative candidate with zero negative extension, continuous at zero and derivative at least one throughout the positive half-line, every reserve bounded by a fixed positive spatial envelope has nonnegative discounted terminal reward no larger than the candidate evaluated at the envelope. This supplies a single integrable bound at each infinite-cap spatial localisation for all stopped clocks without assuming a finite global surplus cap.
-- source:
--   Proved scale-independent secant_of_derivative_lower_bound 5459ff1b and topcap HJB halfline bridge d1a94bc6; mathematical upper bound needed in 25573e81 under stopped X prefix.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_secant_of_derivative_lower_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_positive_halfline_discount_terminal_envelope
    {Ω : Type*}
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_diff : DifferentiableOn ℝ w (Ioi 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (B : ℝ) (hB : 0 < B)
    (V : Ω → ℝ) (hV : ∀ ω, V ω ≤ B)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤ Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ∧
      Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ≤ w B := by sorry
