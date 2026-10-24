-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuousOn_Ici_of_positive_limit
-- name    : AvramDividend.Classical.causal_continuousOn_Ici_of_positive_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:04:40.786605+00:00
-- url     : https://prove2.me/theorems/f405dc8f-d9d5-4cc6-9af9-ee8d60aac61a
-- title:
--   Extend positive-time continuity to time zero using the right-hand limit
-- statement:
--   If f is continuous on strictly positive times and tends to its prescribed value f(0) as x approaches zero from the right, then f is continuous on the whole nonnegative half-line. At the origin, transfer eventual-neighbourhood estimates from the positive to the nonnegative half-line by distinguishing x=0 and x>0. At positive points use continuity on the open set (0,∞). This supplies the final topological bridge for proving Volterra-operator endpoint continuity.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.ContinuousOn
open Set Filter
open scoped Topology

theorem AvramDividend.Classical.causal_continuousOn_Ici_of_positive_limit
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hlim : Tendsto f (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (f 0))) :
    ContinuousOn f (Ici (0 : ℝ)) := by sorry
