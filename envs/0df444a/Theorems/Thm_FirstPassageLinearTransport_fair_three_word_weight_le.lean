-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_fair_three_word_weight_le
-- name    : FirstPassageLinearTransport.fair_three_word_weight_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:15.1028+00:00
-- url     : https://prove2.me/theorems/df1ae3d8-416f-4253-841f-1224b21ad524
-- title:
--   First Passage Linear Transport: fair three word weight le
-- statement:
--   Pointwise three-block form of the fair-to-critical tilt.  A lower bound
--   on the combined terminal sum gives the exponential bin weight.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1768-L1820
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1768-L1820

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.fair_three_word_weight_le
    {a b : ℕ} {center : ℝ}
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool)
    (hterminal : center ≤
      wordIncrementSum collatzLogIncrement u +
        wordIncrementSum collatzLogIncrement v +
        wordIncrementSum collatzLogIncrement w) :
    bernoulliWordWeight (1 / 2) u *
        bernoulliWordWeight (1 / 2) v *
        bernoulliWordWeight (1 / 2) w ≤
      (bernoulliWordWeight collatzTilt u *
        bernoulliWordWeight collatzTilt v *
        bernoulliWordWeight collatzTilt w) *
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * center) := by sorry
