-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_fair_bernoulliWordWeight_change
-- name    : FirstPassageLinearTransport.fair_bernoulliWordWeight_change
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:08.525248+00:00
-- url     : https://prove2.me/theorems/602b2c01-1ec6-5991-b20c-b46e4479cc20
-- title:
--   First Passage Linear Transport: fair bernoulli Word Weight change
-- statement:
--   The First Passage Linear Transport construction uses the fair bernoulli Word Weight change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1758-L1764
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1758-L1764

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.fair_bernoulliWordWeight_change {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by sorry
