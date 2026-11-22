-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_pre1F
-- name    : Comp.CsgQ.mem_pre1F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:58.273049+00:00
-- url     : https://prove2.me/theorems/c5c82040-8ac9-42d7-99cc-341e636bc7dc
-- title:
--   Csg Q: mem pre1 F
-- statement:
--   The Csg Q construction uses the mem pre1 F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L152-L154
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L152-L154

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_pre1F (G : CsgQ S A1 A2) (x : Finset S) (s : S) :
    s ∈ G.pre1F x ↔ ∃ a1, ∀ a2, G.supportF s a1 a2 ⊆ x := by sorry
