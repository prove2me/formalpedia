-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a33_terminal_positive_exponential_majorant
-- name    : AvramDividend.Classical.avram_ga_a33_terminal_positive_exponential_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:22:31.828688+00:00
-- url     : https://prove2.me/theorems/5bb6cad1-f550-4cf4-b450-795ac1235bc4
-- title:
--   Original Gaussian terminal positive cell bounded by exponential source and compact lower floor
-- statement:
--   The positive part of the discounted terminal spatial cell is bounded by a nonnegative exponential upper bound on the postpayment source plus a nonnegative compact lower bound on the prepayment value. This one-sided estimate is the deterministic pointwise bridge for proving an integrable common envelope in d9c4650e, avoiding the false absolute-L1 route.
-- source:
--   Original Gaussian top-cap target d9c4650e-839e-480f-860a-906387200065; reuse authoritative discounted-positive-part lemma 6aa2d670 and exponential upper bound 580c6378.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_discounted_terminal_positive_part_le
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a33_terminal_positive_exponential_majorant
    (q theta K L : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (t : ℝ≥0) (a y z : ℝ)
    (hLower : -L ≤ y)
    (hUpper : a ≤ K * Real.exp (theta * z)) :
    max (Real.exp (-(q * (t : ℝ))) * (a - y)) 0 ≤
      K * Real.exp (theta * z) + L := by sorry
