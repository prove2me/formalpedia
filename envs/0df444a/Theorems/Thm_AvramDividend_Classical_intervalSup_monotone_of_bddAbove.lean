-- Prove2me | Theorems.Thm_AvramDividend_Classical_intervalSup_monotone_of_bddAbove
-- name    : AvramDividend.Classical.intervalSup_monotone_of_bddAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:27:36.782978+00:00
-- url     : https://prove2.me/theorems/6b24051f-d2d0-4bea-aa00-a4f1c403491b
-- title:
--   Monotonicity of locally bounded running suprema
-- statement:
--   For any real-valued function on nonnegative time whose image of every compact initial interval is bounded above, the running supremum on [0,t] is nondecreasing with t. This elementary order fact supports the monotonicity prerequisite for the Stieltjes dividend-measure time-shift identity.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

open Set
open scoped NNReal

theorem AvramDividend.Classical.intervalSup_monotone_of_bddAbove
    (f : ℝ≥0 → ℝ)
    (hb : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t)) :
    Monotone (fun t : ℝ≥0 => sSup (f '' Set.Icc 0 t)) := by sorry
