-- Prove2me | Theorems.Thm_Csg_CSG_bwInd_succ
-- name    : Csg.CSG.bwInd_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:50.51126+00:00
-- url     : https://prove2.me/theorems/14735394-3b63-4c70-ba46-ec66de74f169
-- title:
--   CSG: bw Ind succ
-- statement:
--   The CSG construction uses the bw Ind succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L66-L67
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L66-L67

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.bwInd_succ (rFin : S → ℝ) (n : ℕ) (s : S) :
    C.bwInd rFin (n + 1) s = C.stageValue s (C.bwInd rFin n) := by sorry
