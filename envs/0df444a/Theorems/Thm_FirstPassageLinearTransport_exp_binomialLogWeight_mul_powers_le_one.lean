-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exp_binomialLogWeight_mul_powers_le_one
-- name    : FirstPassageLinearTransport.exp_binomialLogWeight_mul_powers_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:31.3736+00:00
-- url     : https://prove2.me/theorems/7dad8932-f700-489e-a1f8-c47989dd0a47
-- title:
--   First Passage Linear Transport: exp binomial Log Weight mul powers le one
-- statement:
--   The First Passage Linear Transport construction uses the exp binomial Log Weight mul powers le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L558-L576
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L558-L576

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exp_binomialLogWeight_mul_powers_le_one
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Real.exp (binomialLogWeight n k) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by sorry
