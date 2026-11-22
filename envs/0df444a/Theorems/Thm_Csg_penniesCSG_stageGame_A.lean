-- Prove2me | Theorems.Thm_Csg_penniesCSG_stageGame_A
-- name    : Csg.penniesCSG_stageGame_A
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:14:41.882083+00:00
-- url     : https://prove2.me/theorems/e8b203ed-fd32-4019-ac99-489a0036ecff
-- title:
--   Csg: pennies CSG stage Game A
-- statement:
--   The Csg construction uses the pennies CSG stage Game A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L103-L107
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L103-L107

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesCSG_stageGame_A (i j : Fin 2) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).A i j = penniesMatrix.A i j := by sorry
