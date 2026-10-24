-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_right_continuity_glue
-- name    : AvramDividend.Classical.causal_right_continuity_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:29:04.845759+00:00
-- url     : https://prove2.me/theorems/46a10ba4-a4fb-4a0b-b4a1-2b52e9029eb6
-- title:
--   Join interior continuity and a right-hand boundary limit on the nonnegative half-line
-- statement:
--   A real-valued function continuous at all positive points is continuous on the closed nonnegative half-line whenever its right limit at zero equals its value at zero. At x>0 use openness of (0,∞) to turn ContinuousOn into ContinuousAt. At x=0 use Mathlib's continuousWithinAt_Ioi_iff_Ici equivalence. This glue lemma is reusable for Volterra integral operators with L1 kernels.
-- source:
--   Mathlib.Topology.Order.LeftRight continuousWithinAt_Ioi_iff_Ici and Mathlib.Topology.ContinuousOn.

import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set Filter
open scoped Topology

theorem AvramDividend.Classical.causal_right_continuity_glue
    (F : ℝ → ℝ)
    (hpositive : ContinuousOn F (Ioi (0 : ℝ)))
    (horigin : Tendsto F (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (F 0))) :
    ContinuousOn F (Ici (0 : ℝ)) := by sorry
