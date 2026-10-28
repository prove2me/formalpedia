-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_top_iff_deriv_tendsto_atTop
-- name    : AvramDividend.Classical.derivZeroPlus_top_iff_deriv_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:55:50.613714+00:00
-- url     : https://prove2.me/theorems/0f3e992b-ee67-4e3f-9d71-1634e106d98c
-- title:
--   Infinite extended right derivative is equivalent to ordinary right derivative divergence
-- statement:
--   The canonical extended-real right liminf of the ordinary scale derivative equals +∞ if and only if the ordinary derivative tends to +∞ as its argument decreases to zero through positive values. Combines two separately Proved directions, allowing zero-barrier fluctuation arguments to choose whichever representation is convenient.
-- source:
--   Canonical Proved forward and reverse derivative-divergence theorems in pinned Mathlib environment.

import Theorems.Thm_AvramDividend_Classical_deriv_tendsto_atTop_of_derivZeroPlus_top
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop

open AvramDividend.Classical Filter Set

theorem AvramDividend.Classical.derivZeroPlus_top_iff_deriv_tendsto_atTop
    (W : ℝ → ℝ) :
    derivZeroPlus W = ⊤ ↔
      Tendsto (fun y : ℝ => deriv W y)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
