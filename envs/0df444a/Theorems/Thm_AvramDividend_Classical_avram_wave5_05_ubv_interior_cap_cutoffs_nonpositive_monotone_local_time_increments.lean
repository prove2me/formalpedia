-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_interior_cap_cutoffs_nonpositive_monotone_local_time_increments
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_interior_cap_cutoffs_nonpositive_monotone_local_time_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:54:50.720019+00:00
-- url     : https://prove2.me/theorems/600a9dac-6962-4ef1-b1f4-b764ed3b179e
-- title:
--   Every strictly interior cap cutoff has nonpositive Tanaka-style mass against every increasing local-time clock
-- statement:
--   Under strictly interior C2 and gradient w'≥1 and continuous positive finite cap, select a single cap-proximate countable sequence of global uniformly accurate slope-one cutoffs. For each n and every monotone real local-time-like clock L, the derivative kink coefficient 1-w'(b_n) times every nonnegative increment L_t-L_s is nonpositive, including intervals starting at zero or after recurrent cap contact. No derivative at the true cap is used. This is an exact deterministic sign theorem for a potential Itô–Tanaka local-time term; it does NOT assert that the original controlled semimartingale has the corresponding local-time formula or establish finite limits of such terms.
-- source:
--   Proved uniformly cap-proximate cutoffs with exact one-sided finite kink signs ec67fc5b-4a84-433d-b8f3-4fd0edc79443, based on corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged. Compatible with original cap-contact recurrent stopping times 7faa54d0-c54c-4c2d-b5b6-87bb8d2b0fbc.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_interior_cap_cutoffs_nonpositive_monotone_local_time_increments
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c ∧
        c - b n < 1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1)) ∧
      ∀ (n : ℕ) (L : ℝ≥0 → ℝ), Monotone L →
        ∀ (s t : ℝ≥0), s ≤ t →
          (1 - deriv w (b n)) * (L t - L s) ≤ 0 := by sorry
