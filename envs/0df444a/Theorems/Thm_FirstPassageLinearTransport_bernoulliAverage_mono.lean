-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_mono
-- name    : FirstPassageLinearTransport.bernoulliAverage_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:57.940982+00:00
-- url     : https://prove2.me/theorems/823d9e1a-b70f-44d4-85b0-c9f97f1c09b1
-- title:
--   First Passage Linear Transport: bernoulli Average mono
-- statement:
--   The First Passage Linear Transport construction uses the bernoulli Average mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L100-L107
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L100-L107

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliAverage_mono
    {p a₀ a₁ b₀ b₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    bernoulliAverage p a₀ a₁ ≤ bernoulliAverage p b₀ b₁ := by sorry
