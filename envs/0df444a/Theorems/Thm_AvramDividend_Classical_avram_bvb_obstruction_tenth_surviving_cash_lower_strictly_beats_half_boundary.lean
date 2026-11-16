-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_surviving_cash_lower_strictly_beats_half_boundary
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_surviving_cash_lower_strictly_beats_half_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:54:44.715892+00:00
-- url     : https://prove2.me/theorems/46761387-e0ad-4bf8-b0f5-4068a9880c7c
-- title:
--   The original tenth-horizon Stieltjes cash lower bound plus surviving half-unit boundary reward strictly exceeds the candidate
-- statement:
--   Any real discounted cash amount at least (2/25)exp(−1/10), together with the actual survival terminal reward (1/2)exp(−1/10), exceeds the candidate boundary value 1/2. This is the last numerical bridge between the original source clipped dividend cash and the positive-part physical error contradiction.
-- source:
--   The Proved exact positive gap f5055368 states (2/25+1/2)exp(−1/10)>1/2. Replacing the first term by any larger real cash amount preserves strict inequality.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
open Real AvramDividend.Classical

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_surviving_cash_lower_strictly_beats_half_boundary (cash : ℝ)
    (hCash : (2 / 25 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤ cash) :
    (1 / 2 : ℝ) <
      cash + (1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) := by sorry
