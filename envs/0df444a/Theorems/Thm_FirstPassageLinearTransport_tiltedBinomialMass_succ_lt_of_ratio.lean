-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_succ_lt_of_ratio
-- name    : FirstPassageLinearTransport.tiltedBinomialMass_succ_lt_of_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:12.214842+00:00
-- url     : https://prove2.me/theorems/f95e61f2-bf18-43cc-9cf1-25b01c4d8182
-- title:
--   First Passage Linear Transport: tilted Binomial Mass succ lt of ratio
-- statement:
--   The First Passage Linear Transport construction uses the tilted Binomial Mass succ lt of ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L740-L756
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L740-L756

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.tiltedBinomialMass_succ_lt_of_ratio
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k < n)
    (hratio : ((n - k : ℕ) : ℝ) * p <
      ((k + 1 : ℕ) : ℝ) * (1 - p)) :
    tiltedBinomialMass p n (k + 1) < tiltedBinomialMass p n k := by sorry
