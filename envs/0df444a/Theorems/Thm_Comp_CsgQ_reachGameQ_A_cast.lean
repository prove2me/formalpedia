-- Prove2me | Theorems.Thm_Comp_CsgQ_reachGameQ_A_cast
-- name    : Comp.CsgQ.reachGameQ_A_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:40.816949+00:00
-- url     : https://prove2.me/theorems/7a77be6b-d4cf-4a81-b348-eeaed42720ac
-- title:
--   Csg Q: reach Game Q A cast
-- statement:
--   The two stage games agree entrywise: the reward term vanishes by `hr0`, and the expectation is
--       `CsgQ.expect_toCSG`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L136-L144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L136-L144

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

theorem Comp.CsgQ.reachGameQ_A_cast (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).A a1 a2
      = ((G.reachGameQ s v).toMatrixGame).A a1 a2 := by sorry
