-- Prove2me | Theorems.Thm_Comp_CsgQ_answers_sureSafe
-- name    : Comp.CsgQ.answers_sureSafe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:35:42.915741+00:00
-- url     : https://prove2.me/theorems/fc5b3a2f-6e16-4379-a4bb-35659adf0e19
-- title:
--   Csg Q: answers sure Safe
-- statement:
--   **In.** A `sureSafe` objective answered directly from a computed descent: the
--       `Comp/QualitativeFinset.lean` payoff, phrased as an answer. This is the one objective with a
--       generic wrapper, because its chain is a plain `Function.iterate` -- `AF` and `LF` take their
--       outer steps one at a time, so their constructors are the interface instead.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L164-L167
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Objective.lean#L164-L167

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

theorem Comp.CsgQ.answers_sureSafe (G : CsgQ S A1 A2) (h : G.WellFormed) (region c : Finset S) (n : ℕ)
    (hiter : (G.gStepF region)^[n] Finset.univ = c) (hfix : G.gStepF region c = c) :
    G.Answers h (Objective.sureSafe region) (Answer.region c) := by sorry
