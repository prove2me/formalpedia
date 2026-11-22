-- Prove2me | Theorems.Thm_Comp_CsgQ_reachOp_coe_of_goal
-- name    : Comp.CsgQ.reachOp_coe_of_goal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:27:49.100067+00:00
-- url     : https://prove2.me/theorems/ee41876f-62a4-4145-a3bc-5d8b1aff6963
-- title:
--   Csg Q: reach Op coe of goal
-- statement:
--   At a goal state the operator is pinned to `1`, with no game to solve.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L198-L202
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L198-L202

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.reachOp_coe_of_goal (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} (hs : goal s) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ)) = 1 := by sorry
