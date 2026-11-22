-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_supportF
-- name    : Comp.CsgQ.mem_supportF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:47.862829+00:00
-- url     : https://prove2.me/theorems/a8be9a8f-0234-4d8b-bd68-f4b012fa4713
-- title:
--   Csg Q: mem support F
-- statement:
--   The Csg Q construction uses the mem support F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L147-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L147-L149

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) (s' : S) :
    s' ∈ G.supportF s a1 a2 ↔ G.K s a1 a2 s' ≠ 0 := by sorry
