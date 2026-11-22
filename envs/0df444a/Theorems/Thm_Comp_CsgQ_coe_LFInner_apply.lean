-- Prove2me | Theorems.Thm_Comp_CsgQ_coe_LFInner_apply
-- name    : Comp.CsgQ.coe_LFInner_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:29.073822+00:00
-- url     : https://prove2.me/theorems/4bf631f0-ef8f-47d2-8f99-78e4d0806fc0
-- title:
--   Csg Q: coe LFInner apply
-- statement:
--   One turn of the middle chain, as data: `Lpre1(x,y) ∪ b`, matching `CSG.LFInnerFun`'s own
--       shape.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L95-L99
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L95-L99

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.coe_LFInner_apply (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (G.toCSG h).LFInner ↑b ↑y ↑x = (↑(G.lpre1F w x ∪ b) : Set S) := by sorry
