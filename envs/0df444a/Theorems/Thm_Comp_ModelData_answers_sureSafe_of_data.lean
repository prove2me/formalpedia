-- Prove2me | Theorems.Thm_Comp_ModelData_answers_sureSafe_of_data
-- name    : Comp.ModelData.answers_sureSafe_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:50.671207+00:00
-- url     : https://prove2.me/theorems/7c3f2392-9067-4ecf-9eb6-3e3946dee8c4
-- title:
--   Model Data: answers sure Safe of data
-- statement:
--   **A model, an objective, and a computed answer, in one term.** The descent is run over the
--       sparse rows; `hiter` records that it reached `c` and `hfix` that it stopped there; and the
--       conclusion is `Comp/Objective.lean`'s specification relation, whose sure-safety constructor is
--       `CSG.G` on the nose.
--
--       All four hypotheses are decidable statements about concrete data, and three of the four involve
--       no rational arithmetic at all. `Stochastic` is the exception and is needed only here, to make
--       the model a well-formed game.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L138-L147
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L138-L147

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_sureSafe_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates)) (n : ℕ)
    (hiter : (d.gStepOf hs safe)^[n] Finset.univ = c)
    (hfix : d.gStepOf hs safe c = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by sorry
