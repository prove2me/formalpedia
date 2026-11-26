-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_one_eq_two_pow_mul_weight
-- name    : FirstPassageLinearTransport.ballotWordValue_one_eq_two_pow_mul_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:14.723279+00:00
-- url     : https://prove2.me/theorems/3781ae7d-53c7-4a74-997d-ef151b8aa0b8
-- title:
--   First Passage Linear Transport: ballot Word Value one eq two pow mul weight
-- statement:
--   Exact change from the terminal fair multiplicative value to the `3/4`
--   Bernoulli word weight.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3019-L3039
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3019-L3039

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ballotWordValue_one_eq_two_pow_mul_weight :
    ∀ {r : ℕ} (v : Fin r → Bool),
      ballotWordValue 1 v =
        (2 : ℝ) ^ r * bernoulliWordWeight (3 / 4) v := by sorry
