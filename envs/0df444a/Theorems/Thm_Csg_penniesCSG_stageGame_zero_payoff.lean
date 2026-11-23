-- Prove2me | Theorems.Thm_Csg_penniesCSG_stageGame_zero_payoff
-- name    : Csg.penniesCSG_stageGame_zero_payoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:14:41.36968+00:00
-- url     : https://prove2.me/theorems/9476b0d5-cf56-4bf0-8df6-cb11432dac65
-- title:
--   Csg: pennies CSG stage Game zero payoff
-- statement:
--   The Csg construction uses the pennies CSG stage Game zero payoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L109-L112
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L109-L112

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesCSG_stageGame_zero_payoff (x y : Fin 2 → ℝ) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff x y = penniesMatrix.payoff x y := by sorry
