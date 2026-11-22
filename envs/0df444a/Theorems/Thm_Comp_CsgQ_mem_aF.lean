-- Prove2me | Theorems.Thm_Comp_CsgQ_mem_aF
-- name    : Comp.CsgQ.mem_aF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:56:25.659794+00:00
-- url     : https://prove2.me/theorems/d0dcb08d-4300-45dc-8862-942daec4c3b2
-- title:
--   Csg Q: mem a F
-- statement:
--   The Csg Q construction uses the mem a F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L73-L75
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L73-L75

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

theorem Comp.CsgQ.mem_aF (G : CsgQ S A1 A2) (v2 : Finset A2) (y : Finset S) (s : S) (a1 : A1) :
    a1 ∈ G.aF v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ G.supportF s a1 a2 ⊆ y := by sorry
