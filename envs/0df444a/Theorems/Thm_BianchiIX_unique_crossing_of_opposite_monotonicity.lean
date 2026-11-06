-- Prove2me | Theorems.Thm_BianchiIX_unique_crossing_of_opposite_monotonicity
-- name    : BianchiIX.unique_crossing_of_opposite_monotonicity
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:03:07.617101+00:00
-- url     : https://prove2.me/theorems/be788f88-8d35-4f86-bb52-5542459289ed
-- title:
--   Oppositely monotone functions with reversed endpoint order cross exactly once
-- statement:
--   Let $s<t$, and let $V,W:[s,t]\to\mathbb R$ be continuous,
--   with $V$ strictly decreasing and $W$ strictly increasing. If
--   $W(s)<V(s)$ and $V(t)<W(t)$, then there is exactly one
--   $r\in(s,t)$ with $V(r)=W(r)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MonotoneCrossing.lean#L11-L41

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.unique_crossing_of_opposite_monotonicity {V W : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (hV : ContinuousOn V (Icc s t)) (hW : ContinuousOn W (Icc s t))
    (hVa : StrictAntiOn V (Icc s t)) (hWm : StrictMonoOn W (Icc s t))
    (hs : W s < V s) (ht : V t < W t) : ∃! r, r ∈ Ioo s t ∧ V r = W r := by sorry
