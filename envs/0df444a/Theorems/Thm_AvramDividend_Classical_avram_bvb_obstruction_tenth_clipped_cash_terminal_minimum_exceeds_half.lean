-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:37:44.898069+00:00
-- url     : https://prove2.me/theorems/f5055368-b155-48a8-a25b-0a8e40509538
-- title:
--   At T=1/10 the clipped cash supported on (0,2/25] contributes at least (2/25)*exp(−1/10) and the survivor termi
-- statement:
--   At T=1/10 the clipped cash supported on (0,2/25] contributes at least (2/25)*exp(−1/10) and the survivor terminal contributes (1/2)*exp(−1/10). Their sum is strictly greater than w(0)=1/2, giving a source-compatible strictly positive pathwise lower bound.
-- source:
--   Elementary exact rational inequalities; exponential bound uses pinned Real.add_one_le_exp. This is the numeric/source window for the original physical-grid clipped dividend cash contradiction.

import Mathlib
open Real

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half : (1 / 2 : ℝ) <
      (2 / 25 + 1 / 2) * Real.exp (-(1 / 10 : ℝ)) := by sorry
