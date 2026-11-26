-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_binomial_log_mass_le_zero
-- name    : FirstPassageLinearTransport.binomial_log_mass_le_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:30.942705+00:00
-- url     : https://prove2.me/theorems/34349720-41ac-5c0b-8907-ca30f7b6937e
-- title:
--   First Passage Linear Transport: binomial log mass le zero
-- statement:
--   The First Passage Linear Transport construction uses the binomial log mass le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L533-L556
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L533-L556

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.binomial_log_mass_le_zero
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    binomialLogWeight n k + (k : ℝ) * Real.log p +
        ((n - k : ℕ) : ℝ) * Real.log (1 - p) ≤ 0 := by sorry
