-- Prove2me | Theorems.Thm_Csg_penniesMatrix_payoff_col
-- name    : Csg.penniesMatrix_payoff_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:55:09.106883+00:00
-- url     : https://prove2.me/theorems/23474f40-04bc-457f-9027-96924c147b38
-- title:
--   Csg: pennies Matrix payoff col
-- statement:
--   Symmetric counterpart of `penniesMatrix_payoff_row`: against the uniform row strategy, every
--       column strategy also pays exactly `0`. Same `simp only`-not-`simp` reasoning applies.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L70-L72
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L70-L72

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesMatrix_payoff_col (q' : Fin 2 → ℝ) : penniesMatrix.payoff unif2 q' = 0 := by sorry
