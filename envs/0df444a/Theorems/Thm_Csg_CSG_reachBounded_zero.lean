-- Prove2me | Theorems.Thm_Csg_CSG_reachBounded_zero
-- name    : Csg.CSG.reachBounded_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:24.845162+00:00
-- url     : https://prove2.me/theorems/589fbe4d-ad8b-465e-a0ab-23ae532db73e
-- title:
--   CSG: reach Bounded zero
-- statement:
--   The CSG construction uses the reach Bounded zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L53-L54
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BoundedReachability.lean#L53-L54

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.reachBounded_zero (goal : S → Prop) [DecidablePred goal] (s : S) :
    C.reachBounded goal 0 s = if goal s then 1 else 0 := by sorry

attribute [defeq] Csg.CSG.reachBounded_zero
