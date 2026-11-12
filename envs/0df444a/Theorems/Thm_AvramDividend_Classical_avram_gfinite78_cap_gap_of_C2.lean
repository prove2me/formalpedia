-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite78_cap_gap_of_C2
-- name    : AvramDividend.Classical.avram_gfinite78_cap_gap_of_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:09:33.617411+00:00
-- url     : https://prove2.me/theorems/3060cf3d-5b1f-4b01-a0b7-ccdab4cbbd2b
-- title:
--   Nonnegative finite-cap excess gap from interior C2 regularity
-- statement:
--   If the dividend verification candidate is continuous on a compact cap interval, twice continuously differentiable on its interior, and has derivative at least one throughout that interior, then its finite-cap cash defect is nonnegative. This discharges the positivity needed before applying the stopped Gaussian eventwise L1 cash transfer theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad
open Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_gfinite78_cap_gap_of_C2
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hsmooth : ContDiffOn ℝ 2 w (Ioo a b))
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    0 ≤ (w b - w a) - (b - a) := by
  sorry
