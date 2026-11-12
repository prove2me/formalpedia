-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB95_real_halfopen_interval_finite_partition
-- name    : AvramDividend.Classical.avram_gbB95_real_halfopen_interval_finite_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:46:02.663469+00:00
-- url     : https://prove2.me/theorems/61419cbc-655f-4554-93e3-f92d57aa3c75
-- title:
--   A half-open real interval is partitioned by finitely many equal-width subintervals
-- statement:
--   For positive width δ, the indicator of [a,a+bδ) is the sum of the indicators of its b consecutive half-open cells. The equality holds at every real time t.
-- source:
--   Elementary real interval partition child feeding original-grid B93 and B91.

import Mathlib

theorem AvramDividend.Classical.avram_gbB95_real_halfopen_interval_finite_partition
    (a δ t : ℝ) (hδ : 0 < δ) (b : ℕ) :
    (if a ≤ t ∧ t < a + (b : ℝ) * δ then (1 : ℝ) else 0) =
    (Finset.range b).sum (fun j =>
      if a + (j : ℝ) * δ ≤ t ∧
        t < a + ((j + 1 : ℕ) : ℝ) * δ
      then (1 : ℝ) else 0) := by sorry
