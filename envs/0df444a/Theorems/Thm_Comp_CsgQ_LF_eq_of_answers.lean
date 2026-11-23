-- Prove2me | Theorems.Thm_Comp_CsgQ_LF_eq_of_answers
-- name    : Comp.CsgQ.LF_eq_of_answers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:36:23.601127+00:00
-- url     : https://prove2.me/theorems/0a68a8f9-b0d8-48d6-b95b-e8e2cee26209
-- title:
--   Csg Q: LF eq of answers
-- statement:
--   **Out.** And for limit-sure reachability, the value-1 set.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L185-L189
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L185-L189

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

theorem Comp.CsgQ.LF_eq_of_answers (G : CsgQ S A1 A2) (h : G.WellFormed) {target c : Finset S}
    (ha : G.Answers h (Objective.limitReach target) (Answer.region c)) :
    (G.toCSG h).LF ↑target = (↑c : Set S) := by sorry
