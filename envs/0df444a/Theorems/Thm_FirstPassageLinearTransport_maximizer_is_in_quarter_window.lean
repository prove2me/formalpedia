-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_maximizer_is_in_quarter_window
-- name    : FirstPassageLinearTransport.maximizer_is_in_quarter_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:22.572354+00:00
-- url     : https://prove2.me/theorems/d3258f9a-3a9c-465a-9434-77a21d476be0
-- title:
--   First Passage Linear Transport: maximizer is in quarter window
-- statement:
--   The First Passage Linear Transport construction uses the maximizer is in quarter window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L758-L822
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L758-L822

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.maximizer_is_in_quarter_window
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3)
    {n k₀ : ℕ} (hn : 9 ≤ n) (hk₀n : k₀ ≤ n)
    (hmax : ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀) :
    (n : ℝ) / 4 ≤ (k₀ : ℝ) ∧
      (n : ℝ) / 4 ≤ ((n - k₀ : ℕ) : ℝ) := by sorry
