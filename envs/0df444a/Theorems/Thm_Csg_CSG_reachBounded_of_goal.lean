-- Prove2me | Theorems.Thm_Csg_CSG_reachBounded_of_goal
-- name    : Csg.CSG.reachBounded_of_goal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:14:22.723998+00:00
-- url     : https://prove2.me/theorems/d2876b1b-0033-4341-9936-3eb0876d59b0
-- title:
--   CSG: reach Bounded of goal
-- statement:
--   A `goal` state is worth `1` at *every* step budget, not just `0` -- the whole point of folding
--       the absorption check into every level rather than only the base case.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L62-L66
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L62-L66

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachBounded_of_goal (goal : S → Prop) [DecidablePred goal] (k : ℕ) {s : S}
    (hs : goal s) : C.reachBounded goal k s = 1 := by sorry
