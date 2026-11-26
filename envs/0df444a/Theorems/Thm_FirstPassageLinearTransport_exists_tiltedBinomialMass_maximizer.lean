-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_maximizer
-- name    : FirstPassageLinearTransport.exists_tiltedBinomialMass_maximizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:28.740164+00:00
-- url     : https://prove2.me/theorems/087bdf34-36ec-44be-88d6-5d28eb4226ed
-- title:
--   First Passage Linear Transport: exists tilted Binomial Mass maximizer
-- statement:
--   The First Passage Linear Transport construction uses the exists tilted Binomial Mass maximizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L824-L834
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L824-L834

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_tiltedBinomialMass_maximizer (p : ℝ) (n : ℕ) :
    ∃ k₀ : ℕ, k₀ ≤ n ∧ ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := by sorry
