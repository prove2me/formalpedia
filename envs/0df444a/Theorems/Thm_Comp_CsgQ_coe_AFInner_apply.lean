-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_AFInner_apply
-- name    : Comp.CsgQ.coe_AFInner_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:33.101826+00:00
-- url     : https://prove2.me/theorems/57caffd0-fcfa-4a04-a17a-7d4575c8c2c6
-- title:
--   Csg Q: coe AFInner apply
-- statement:
--   The Csg Q construction uses the coe AFInner apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L82-L85
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L82-L85

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_AFInner_apply (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S) :
    (G.toCSG h).AFInner ↑b ↑y ↑x = (↑(G.afStepF b y x) : Set S) := by sorry
