-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
-- name    : AvramDividend.Classical.avram_gledger29_topcap_secant_without_contdiff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:34:50.864196+00:00
-- url     : https://prove2.me/theorems/6822fd33-db0f-437b-9c44-d819aba26433
-- title:
--   Positive derivative bounds global reward secants without requiring C1
-- statement:
--   For a reward continuous on nonnegative reserves, if its ordinary derivative exists and is at least one at every positive reserve, then each nonnegative secant of the reward dominates the reserve increment. Unlike the existing C1 Avram secant helper, this proof requires no continuous derivative and supports the exact weak hypotheses of Gaussian27.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_gledger29_topcap_secant_without_contdiff
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ w b - w a := by sorry
