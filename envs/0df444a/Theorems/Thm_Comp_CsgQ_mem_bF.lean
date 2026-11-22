-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_bF
-- name    : Comp.CsgQ.mem_bF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:56:32.998566+00:00
-- url     : https://prove2.me/theorems/2789d087-4870-48ac-854c-e982d4db126d
-- title:
--   Csg Q: mem b F
-- statement:
--   The Csg Q construction uses the mem b F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L94-L96
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L94-L96

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.mem_bF (G : CsgQ S A1 A2) (v1 : Finset A1) (x : Finset S) (s : S) (a2 : A2) :
    a2 ∈ G.bF v1 x s ↔ ∃ a1 ∈ v1, (G.supportF s a1 a2 ∩ x).Nonempty := by sorry
