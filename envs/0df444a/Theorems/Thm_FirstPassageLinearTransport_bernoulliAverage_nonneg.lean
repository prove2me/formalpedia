-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_nonneg
-- name    : FirstPassageLinearTransport.bernoulliAverage_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:59.249309+00:00
-- url     : https://prove2.me/theorems/795c153f-8aee-5855-b393-98f86272e397
-- title:
--   First Passage Linear Transport: bernoulli Average nonneg
-- statement:
--   The First Passage Linear Transport construction uses the bernoulli Average nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L84-L91
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L84-L91

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliAverage_nonneg
    {p x₀ x₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) :
    0 ≤ bernoulliAverage p x₀ x₁ := by sorry
