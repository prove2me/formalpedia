-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_tiltedBinomialMass_le_sqrt_of_quarter
-- name    : FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt_of_quarter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:42.983495+00:00
-- url     : https://prove2.me/theorems/f1583f57-cca3-442c-892f-b8c9f280daaf
-- title:
--   First Passage Linear Transport: exists tilted Binomial Mass le sqrt of quarter
-- statement:
--   The First Passage Linear Transport construction uses the exists tilted Binomial Mass le sqrt of quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L582-L653
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L582-L653

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_tiltedBinomialMass_le_sqrt_of_quarter
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 0 < n → 0 < k → k < n →
        (n : ℝ) / 4 ≤ (k : ℝ) →
        (n : ℝ) / 4 ≤ ((n - k : ℕ) : ℝ) →
        tiltedBinomialMass p n k ≤ C / Real.sqrt n := by sorry
