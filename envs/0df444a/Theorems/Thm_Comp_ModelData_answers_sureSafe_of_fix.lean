-- Prove2me | Theorems.Thm_Comp_ModelData_answers_sureSafe_of_fix
-- name    : Comp.ModelData.answers_sureSafe_of_fix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:20:10.940021+00:00
-- url     : https://prove2.me/theorems/8747586c-faf8-424c-b87e-18fbc9b394c6
-- title:
--   Model Data: answers sure Safe of fix
-- statement:
--   **A model, an objective, and a computed answer -- with nothing counted and nothing certified.**
--       The caller names the region and says, by one decidable check, that it is what the loop returned.
--
--       Compare `answers_sureSafe_of_data`, which wants an iteration count *and* a fixed-point check.
--       Both are gone: the count because the loop stops on its own, the check because the loop is proved
--       to stop. What is left is the one thing a caller genuinely has to say -- which `Finset` it is
--       claiming the answer to be.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L189-L194
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L189-L194

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_sureSafe_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (safe c : Finset (Fin d.nStates))
    (hc : d.gRegion hs safe = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.sureSafe safe) (Answer.region c) := by sorry
