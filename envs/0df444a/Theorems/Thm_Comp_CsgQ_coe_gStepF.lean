-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_gStepF
-- name    : Comp.CsgQ.coe_gStepF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:53:07.988041+00:00
-- url     : https://prove2.me/theorems/47fd2d49-1500-4d04-8d86-719cc3d431cd
-- title:
--   Csg Q: coe g Step F
-- statement:
--   `gStepF` is `GStepQ` under `Finset.coe` -- `coe_pre1F` intersected with `safe`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L95-L97
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L95-L97

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_gStepF (G : CsgQ S A1 A2) (safe x : Finset S) :
    (↑(G.gStepF safe x) : Set S) = G.GStepQ ↑safe ↑x := by sorry
