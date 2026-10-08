-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
-- name    : AvramDividend.Classical.rightLimit_eq_of_monotone_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:19:34.818645+00:00
-- url     : https://prove2.me/theorems/1785b131-19ec-441f-aa95-91ad00832a89
-- title:
--   Strict-right dividend infimum equals current dividends for a right-continuous monotone path
-- statement:
--   For any real-valued nondecreasing dividend path on nonnegative time, continuity from the right at t implies that its right limit, defined as the infimum of dividends at strictly later times, equals the current dividends at t. This turns the no-right-dividend-jumps condition needed for admissibility into an ordinary pathwise right-continuity condition.
-- source:
--   Mathematical bridge from the right-continuity of the barrier running maximum to the formal dividend admissibility inequality; relies on Mathlib Monotone.rightLim_eq_sInf and ContinuousWithinAt.rightLim_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.rightLimit_eq_of_monotone_right_continuous {Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hmono : Monotone (fun s => D s ω))
    (hr : ContinuousWithinAt (fun s => D s ω) (Ici t) t) :
    rightLimit D t ω = D t ω := by
  sorry
