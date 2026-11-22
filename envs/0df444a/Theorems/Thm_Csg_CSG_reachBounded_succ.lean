-- Prove2me | Theorems.Thm_Csg_CSG_reachBounded_succ
-- name    : Csg.CSG.reachBounded_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:46:21.5958+00:00
-- url     : https://prove2.me/theorems/e14ffb35-923b-45ff-b54b-b4afbb20c69b
-- title:
--   CSG: reach Bounded succ
-- statement:
--   The CSG construction uses the reach Bounded succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L56-L58
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L56-L58

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachBounded_succ (goal : S → Prop) [DecidablePred goal] (k : ℕ) (s : S) :
    C.reachBounded goal (k + 1) s =
      if goal s then 1 else C.stageValue s (C.reachBounded goal k) := by sorry
