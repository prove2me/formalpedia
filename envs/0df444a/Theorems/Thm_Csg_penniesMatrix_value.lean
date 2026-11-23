-- Prove2me | Theorems.Thm_Csg_penniesMatrix_value
-- name    : Csg.penniesMatrix_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:25:02.75045+00:00
-- url     : https://prove2.me/theorems/f6c3be8b-eae6-4b21-913e-53a8cbf19df4
-- title:
--   Csg: pennies Matrix value
-- statement:
--   **The payoff, part one.** Matching pennies has value exactly `0` -- the textbook answer, not
--       an approximation of it. Uniform vs. uniform is a saddle point (both no-improvement conditions
--       are equalities, `0 ≤ 0`, from `penniesMatrix_payoff_row`/`_col`), so `value_unique` pins the
--       value down exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L78-L88
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L78-L88

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesMatrix_value : penniesMatrix.value = 0 := by sorry
