-- Prove2me | Theorems.Thm_Comp_CsgQ_not_answers_discounted_region
-- name    : Comp.CsgQ.not_answers_discounted_region
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:06:25.968045+00:00
-- url     : https://prove2.me/theorems/3e5a97cd-be5d-4b56-b475-f723daeda94a
-- title:
--   Csg Q: not answers discounted region
-- statement:
--   **The indices do work.** A region is not a possible answer to a discounted value, and the
--       relation says so by having no constructor with those indices -- so this is unprovable rather
--       than false, and the same holds of every other mismatched pair. That is the benefit of indexing
--       the relation by both the question and the answer shape instead of by the question alone.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L195-L198
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L195-L198

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

theorem Comp.CsgQ.not_answers_discounted_region (G : CsgQ S A1 A2) (h : G.WellFormed) (l : ℚ)
    (c : Finset S) : ¬ G.Answers h (Objective.discounted l) (Answer.region c) := by sorry
