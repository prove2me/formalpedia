-- Prove2me | Theorems.Thm_Comp_CsgQ_le_lfInner_of_step
-- name    : Comp.CsgQ.le_lfInner_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:01:50.993458+00:00
-- url     : https://prove2.me/theorems/ddbd22d3-d483-4bbf-b6e4-89cec267f2d4
-- title:
--   Csg Q: le lf Inner of step
-- statement:
--   One middle step is sound: from a lower bound `x` on the `μX` fixed point, the next computed
--       region is still a lower bound. `Comp/QualitativeLimitFinset.lean`'s climb, one level out.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L103-L109
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean#L103-L109

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.le_lfInner_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1))
    (hle : (↑x : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp)
    (hc : c = G.lpre1F w x ∪ b) :
    (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp := by sorry
