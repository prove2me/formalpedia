-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_locally_stable_of_rightCont_positive
-- name    : AvramDividend.Classical.chat04_closed_survival_locally_stable_of_rightCont_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:33:29.94245+00:00
-- url     : https://prove2.me/theorems/0785fee2-1896-4c05-ab2f-8ffbcbe28076
-- title:
--   Local stability of closed-horizon survival at a positive right-continuous reserve
-- statement:
--   If a real-valued path on nonnegative time is right-continuous at time t, is strictly positive there, and has remained nonnegative up to t, then survival remains true through every sufficiently close later horizon. This supplies the nonzero-reward mask-stability hypothesis for the killed-scale right-continuity proof.
-- source:
--   Mathlib mem_nhdsGE_iff_exists_Ico_subset and continuity within the right neighbourhood at t.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightNhds

open Filter Set Topology

theorem AvramDividend.Classical.chat04_closed_survival_locally_stable_of_rightCont_positive
    (f : NNReal → ℝ) (t : NNReal)
    (hfcont : ContinuousWithinAt f (Ici t) t)
    (htpos : 0 < f t)
    (htsurv : ∀ s : NNReal, s ≤ t → 0 ≤ f s) :
    ∀ᶠ u in 𝓝[Ici t] t, ∀ s : NNReal, s ≤ u → 0 ≤ f s := by sorry
