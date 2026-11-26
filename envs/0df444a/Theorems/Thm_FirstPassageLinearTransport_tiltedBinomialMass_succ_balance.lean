-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_succ_balance
-- name    : FirstPassageLinearTransport.tiltedBinomialMass_succ_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:58.872424+00:00
-- url     : https://prove2.me/theorems/0b50d5f9-7bf7-4009-b6df-9c6488c628b1
-- title:
--   First Passage Linear Transport: tilted Binomial Mass succ balance
-- statement:
--   The First Passage Linear Transport construction uses the tilted Binomial Mass succ balance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L655-L677
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L655-L677

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.tiltedBinomialMass_succ_balance
    {p : ℝ} {n k : ℕ} (hkn : k < n) :
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) =
      ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k := by sorry
