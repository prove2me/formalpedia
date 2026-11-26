-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_lt_succ_of_ratio
-- name    : FirstPassageLinearTransport.tiltedBinomialMass_lt_succ_of_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:08.068805+00:00
-- url     : https://prove2.me/theorems/323e4a9f-5eb1-535d-9414-e99b1b42935e
-- title:
--   First Passage Linear Transport: tilted Binomial Mass lt succ of ratio
-- statement:
--   The First Passage Linear Transport construction uses the tilted Binomial Mass lt succ of ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L722-L738
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L722-L738

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.tiltedBinomialMass_lt_succ_of_ratio
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k < n)
    (hratio : ((k + 1 : ℕ) : ℝ) * (1 - p) <
      ((n - k : ℕ) : ℝ) * p) :
    tiltedBinomialMass p n k < tiltedBinomialMass p n (k + 1) := by sorry
