-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_gStepF
-- name    : Comp.CsgQ.mem_gStepF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:59.518368+00:00
-- url     : https://prove2.me/theorems/a3ee7c0c-27fc-4b98-83d2-d7bad5b5b12e
-- title:
--   Csg Q: mem g Step F
-- statement:
--   The Csg Q construction uses the mem g Step F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L157-L159
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L157-L159

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_gStepF (G : CsgQ S A1 A2) (safe x : Finset S) (s : S) :
    s ∈ G.gStepF safe x ↔ s ∈ G.pre1F x ∧ s ∈ safe := by sorry
