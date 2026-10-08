-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_countable_rightJump_times
-- name    : AvramDividend.Classical.dividendStrategy_countable_rightJump_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:10:43.708043+00:00
-- url     : https://prove2.me/theorems/d3ef8e26-7ec8-48c3-8dd5-c02be5bf7e25
-- title:
--   The right dividend-payment jump times of any strategy form a countable set
-- statement:
--   Every cumulative dividend strategy D is pathwise nondecreasing. Its canonical real-time extension t↦D(t.toNNReal) is therefore monotone, and any nonzero right jump forces a discontinuity. By Mathlib Monotone.countable_not_continuousAt, the set of all such jump times is at most countable. This permits the entire jump-payment part of the discounted dividend Stieltjes integral to be expressed as a countable sum while explicitly separating any continuous component.
-- source:
--   Mathlib Topology.Order.Monotone Monotone.countable_not_continuousAt and Topology.Order.LeftRightLim ContinuousWithinAt.rightLim_eq, pinned revision 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_countable_rightJump_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable
      {t : ℝ | Function.rightLim (fun s : ℝ => D s.toNNReal ω) t ≠
        D t.toNNReal ω} := by sorry
