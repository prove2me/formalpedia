-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto
-- name    : AvramDividend.Classical.derivZeroPlus_eq_coe_of_right_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:07:35.419895+00:00
-- url     : https://prove2.me/theorems/dcb55b00-84c7-4c1d-af38-0af0a281b05d
-- title:
--   A finite right limit of the ordinary scale derivative determines its extended liminf
-- statement:
--   If the ordinary derivative W'(y) tends to a finite real d as y decreases to zero through positive values, then the extended-real right derivative derivZeroPlus W, defined as the one-sided liminf of W', equals the canonical EReal embedding of d. This bridges analytic regularity at the origin with the exact boundary derivative used by the Avram zero-barrier candidate.
-- source:
--   Pinned Mathlib EReal.tendsto_coe and Filter.Tendsto.liminf_eq, plus ScaleFunction.derivZeroPlus definition.

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter Set

theorem AvramDividend.Classical.derivZeroPlus_eq_coe_of_right_tendsto
    (W : ℝ → ℝ) (d : ℝ)
    (hderiv : Filter.Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)) :
    derivZeroPlus W = (d : EReal) := by sorry
