-- Prove2me | Theorems.Thm_Comp_CsgQ_G_eq_of_answers
-- name    : Comp.CsgQ.G_eq_of_answers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:04:39.280148+00:00
-- url     : https://prove2.me/theorems/fb73b349-be79-46a2-a463-b47b2947568f
-- title:
--   Csg Q: G eq of answers
-- statement:
--   **Out.** An answer to a `sureSafe` objective is the sure-safety region, with nothing else
--       assumed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L171-L175
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L171-L175

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_Reach
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_Objective
set_option autoImplicit true
open Comp
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.G_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {region c : Finset S}
    (ha : G.Answers h (Objective.sureSafe region) (Answer.region c)) :
    (G.toCSG h).G ↑region = (↑c : Set S) := by sorry
