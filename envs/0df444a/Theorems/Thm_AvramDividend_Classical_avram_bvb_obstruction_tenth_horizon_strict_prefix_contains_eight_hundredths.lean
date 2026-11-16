-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:31:18.940421+00:00
-- url     : https://prove2.me/theorems/5559625f-02a7-48c4-872f-ebe2661f7227
-- title:
--   At each physical mesh index n≥4, the strict cash cut-off T−δ_n for T=1/10 strictly exceeds 2/25. Thus the full
-- statement:
--   At each physical mesh index n≥4, the strict cash cut-off T−δ_n for T=1/10 strictly exceeds 2/25. Thus the full Stieltjes measure of (0,2/25] occurs inside the original strict paymentTimes prefix at all those n.
-- source:
--   Elementary exact rational inequalities; exponential bound uses pinned Real.add_one_le_exp. This is the numeric/source window for the original physical-grid clipped dividend cash contradiction.

import Mathlib
open Real

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths (n : ℕ) (hn : 4 ≤ n) :
      (2 / 25 : ℝ) < 1 / 10 - (1 / 10) / ((n : ℝ) + 2) := by sorry
