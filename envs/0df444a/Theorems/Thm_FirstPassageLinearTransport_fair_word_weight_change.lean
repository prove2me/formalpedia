-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_fair_word_weight_change
-- name    : FirstPassageLinearTransport.fair_word_weight_change
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:06.264971+00:00
-- url     : https://prove2.me/theorems/e3037a58-6f62-42b6-be2a-9bb057cf062f
-- title:
--   First Passage Linear Transport: fair word weight change
-- statement:
--   Exact finite-word change of weights.  This is the algebraic identity
--   behind equation (B.5), stated without any infinite product measure.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1702-L1746
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1702-L1746

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.fair_word_weight_change {m : ℕ} (v : Fin m → Bool) :
    (1 / 2 : ℝ) ^ m =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by sorry
