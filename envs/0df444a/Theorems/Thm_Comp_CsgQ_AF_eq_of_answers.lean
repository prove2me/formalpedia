-- Prove2me | Theorems.Thm_Comp_CsgQ_AF_eq_of_answers
-- name    : Comp.CsgQ.AF_eq_of_answers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:36:10.233559+00:00
-- url     : https://prove2.me/theorems/a830542a-2ba8-4cc7-93e5-878385175126
-- title:
--   Csg Q: AF eq of answers
-- statement:
--   **Out.** Likewise for almost-sure reachability.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L178-L182
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L178-L182

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

theorem Comp.CsgQ.AF_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {target c : Finset S}
    (ha : G.Answers h (Objective.almostReach target) (Answer.region c)) :
    (G.toCSG h).AF ↑target = (↑c : Set S) := by sorry
