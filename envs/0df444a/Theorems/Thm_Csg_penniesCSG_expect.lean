-- Prove2me | Theorems.Thm_Csg_penniesCSG_expect
-- name    : Csg.penniesCSG_expect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:14:38.759489+00:00
-- url     : https://prove2.me/theorems/e9225c80-15da-490f-a916-304c9689270b
-- title:
--   Csg: pennies CSG expect
-- statement:
--   The Csg construction uses the pennies CSG expect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L98-L101
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L98-L101

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesCSG_expect (i j : Fin 2) (v : Unit → ℝ) :
    penniesCSG.expect () i j v = v () := by sorry
