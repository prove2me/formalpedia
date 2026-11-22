-- Prove2me | Theorems.Thm_Comp_CsgQ_LF_eq_coe_of_fixed
-- name    : Comp.CsgQ.LF_eq_coe_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:03:22.753175+00:00
-- url     : https://prove2.me/theorems/e7e1b07a-96ab-4dac-bfa8-313ef3dac249
-- title:
--   Csg Q: LF eq coe of fixed
-- statement:
--   **The value-1 set, exactly.** A region that is its own certified `μX` fixed point and that the
--       outer descent has reached *is* `LF b` -- the limit-sure reachability set of the real-valued
--       game, hence its set of value-1 states for reaching `b`.
--
--       Nothing in the chain of hypotheses bounds any of the three iteration counts. Each level was run,
--       seen to stop, and checked.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L149-L156
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L149-L156

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.LF_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S)
    (hinner : ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑y : Set S))
    (hy : (G.toCSG h).LF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).LF ↑b = (↑y : Set S) := by sorry
