-- Prove2me | Theorems.Thm_Csg_penniesMatrix_payoff_row
-- name    : Csg.penniesMatrix_payoff_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:54.959166+00:00
-- url     : https://prove2.me/theorems/5fc7ea05-ae5a-4984-9973-ce3707e585d5
-- title:
--   Csg: pennies Matrix payoff row
-- statement:
--   Against the uniform column strategy, *every* row strategy pays exactly `0` -- not just an
--       inequality, an identity, since each row of the payoff matrix already sums to `0`. Holds for
--       any `p' : Fin 2 → ℝ` whatsoever, no simplex membership needed: it's the payoff matrix's row
--       sums vanishing, not a convexity argument. Deliberately `simp only`, not plain `simp`: the
--       default simp set includes `Fin.sum_univ_two`, which would expand both finite sums into
--       concrete numeral terms *before* the abstract `penniesMatrix_row_sum_zero` gets a chance to
--       fire on the still-general `∑ j, penniesMatrix.A i j` pattern, leaving a residual goal neither
--       lemma can close. Naming the exact lemmas needed, in the order they're needed, avoids that
--       ordering trap.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L64-L66
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L64-L66

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesMatrix_payoff_row (p' : Fin 2 → ℝ) : penniesMatrix.payoff p' unif2 = 0 := by sorry
