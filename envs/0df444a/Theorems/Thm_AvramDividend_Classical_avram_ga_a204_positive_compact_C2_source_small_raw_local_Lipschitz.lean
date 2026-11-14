-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
-- name    : AvramDividend.Classical.avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:36:49.985931+00:00
-- url     : https://prove2.me/theorems/abb684a9-ca05-4636-b5f0-e46e0a53bfa8
-- title:
--   Positive compact Gaussian stopped source C2 band yields a uniform local Lipschitz bound for every sufficiently small raw increment
-- statement:
--   Let a C2 value function be smooth on strictly positive reserves and consider any compact reserve band from a to b with positive a. By the already Proved original compact ContDiffOn Lipschitz theorem, there exists a uniform constant L valid for all raw physical source increments with absolute size strictly less than half a, with starting reserve anywhere inside the original compact band. This supplies the small Gaussian raw-cell Lipschitz premise for the mathematically sound discount-source repair a199 directly from the original gledger137 stopped postpayment band, without artificially assuming global Lipschitz regularity.
-- source:
--   Already Proved avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz on a larger positive compact reserve interval.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ContDiffOn_compact_band_exists_lipschitz
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc a b, ∀ r : ℝ, |r| < a / 2 →
      |w (y + r) - w y| ≤ L * |r| := by sorry
