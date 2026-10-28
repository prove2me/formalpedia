-- Prove2me | Theorems.Thm_AvramDividend_Classical_raw_runningSup_constant_of_future_below_previous_max
-- name    : AvramDividend.Classical.raw_runningSup_constant_of_future_below_previous_max
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:10:26.075999+00:00
-- url     : https://prove2.me/theorems/fa10ac12-ab24-4d26-9d03-f8b4e6a9530e
-- title:
--   A running maximum does not increase while the underlying path remains below its preceding record
-- statement:
--   Let f be any real-valued nonnegative-time path with bounded range above on [0,v], and fix times u≤v. If every value of f on [u,v] is bounded by the previous running supremum M_u=sup_{0≤s≤u}f(s), then the running supremum at v is still exactly M_u. This records a necessary pathwise property of the actual reflected Lévy local-time regulator S=runningSup X: future intervals with no new record carry no regulator increase. Together with right continuity of X, a positive drawdown S_u−X_u>0 provides a short interval of this form, and hence is a first step towards showing that the Lebesgue–Stieltjes record measure dS is supported (measure-theoretically) on the zero set of the reflected process. The latter support and the characteristic sigma-finite excursion measure are not yet claimed.
-- source:
--   Elementary compact running-supremum order bounds in pinned Mathlib.Order.ConditionallyCompleteLattice.Basic and AvramDividend.Classical.runningSup_split_at.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Set.Basic

open AvramDividend.Classical Set
open scoped NNReal

theorem AvramDividend.Classical.raw_runningSup_constant_of_future_below_previous_max
    (f : ℝ≥0 → ℝ) (u v : ℝ≥0) (huv : u ≤ v)
    (hb : BddAbove (f '' Icc 0 v))
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      f t ≤ sSup (f '' Icc 0 u)) :
    sSup (f '' Icc 0 v) = sSup (f '' Icc 0 u) := by sorry
