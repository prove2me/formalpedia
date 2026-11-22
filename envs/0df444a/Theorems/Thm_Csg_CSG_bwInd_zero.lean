-- Prove2me | Theorems.Thm_Csg_CSG_bwInd_zero
-- name    : Csg.CSG.bwInd_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:42:19.023923+00:00
-- url     : https://prove2.me/theorems/6d083276-fa95-4546-b1ef-13c31284264d
-- title:
--   CSG: bw Ind zero
-- statement:
--   The CSG construction uses the bw Ind zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L64-L64
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/BackwardInduction.lean#L64-L64

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)

theorem Csg.CSG.bwInd_zero (rFin : S → ℝ) : C.bwInd rFin 0 = rFin := by sorry

attribute [defeq] Csg.CSG.bwInd_zero
