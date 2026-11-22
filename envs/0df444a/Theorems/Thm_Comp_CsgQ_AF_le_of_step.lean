-- Prove2me | Theorems.Thm_Comp_CsgQ_AF_le_of_step
-- name    : Comp.CsgQ.AF_le_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:58:36.019474+00:00
-- url     : https://prove2.me/theorems/ada4c279-1be9-4139-a159-a52724a87c43
-- title:
--   Csg Q: AF le of step
-- statement:
--   One outer step, given the certified `μX` fixed point at `y`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L117-L124
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean#L117-L124

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.AF_le_of_step (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b ≤ (↑c : Set S) := by sorry
