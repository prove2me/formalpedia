-- Prove2me | Theorems.Thm_Csg_idsCSG_payoff_row
-- name    : Csg.idsCSG_payoff_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:02.834878+00:00
-- url     : https://prove2.me/theorems/4f4fa026-c294-49e9-bd51-b002bfc4eab4
-- title:
--   Csg: ids CSG payoff row
-- statement:
--   Against `idsQ`, *every* row strategy pays exactly `idsV1 s` -- `idsQ` equalises the two pure
--       row actions' payoffs at whichever state `s` is (checked directly, by cases, since there are
--       only two of each), so any weighted average of them is that same constant. Mirrors
--       `RockPaperScissors.lean`'s `rpsCSG_stageGame_initial_payoff_row`, generalised from the uniform
--       `unif3` to the non-uniform `idsQ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L184-L195
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L184-L195

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_payoff_row (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff p' idsQ = idsV1 s := by sorry
