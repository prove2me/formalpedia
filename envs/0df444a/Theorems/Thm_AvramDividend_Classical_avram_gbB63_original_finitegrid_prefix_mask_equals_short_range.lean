-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
-- name    : AvramDividend.Classical.avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:55:32.93989+00:00
-- url     : https://prove2.me/theorems/c6c99075-31ab-479d-8239-dd518cbc033c
-- title:
--   An original physical-grid strict-left stopping mask is exactly a shortened finite prefix sum
-- statement:
--   For any original physical grid with m+1 cells and a pathwise stopping index k≤m+1, its exact left-start stopping mask selecting cells i<k turns a full finite mesh sum into the unmasked sum over the first k cells. This finite-prefix identity is used to transfer the Abel discounted Brownian increment bound to the original strict-left stopped Gaussian source, including the case k=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
    (m k : ℕ) (hk : k ≤ m + 1) (f : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      if i < k then f i else 0) =
    (Finset.range k).sum f := by sorry
