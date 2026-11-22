-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_apre1F
-- name    : Comp.CsgQ.mem_apre1F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:57:48.165812+00:00
-- url     : https://prove2.me/theorems/97ad9f4b-dc49-4a38-a628-28ea68989532
-- title:
--   Csg Q: mem apre1 F
-- statement:
--   The Csg Q construction uses the mem apre1 F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L65-L67
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L65-L67

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_apre1F (G : CsgQ S A1 A2) (x y : Finset S) (s : S) :
    s ∈ G.apre1F x y ↔ G.bF (G.aF ∅ y s) x s = Finset.univ := by sorry
