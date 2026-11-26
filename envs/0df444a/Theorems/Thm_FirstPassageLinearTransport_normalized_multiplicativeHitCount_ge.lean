-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_multiplicativeHitCount_ge
-- name    : FirstPassageLinearTransport.normalized_multiplicativeHitCount_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:20.895415+00:00
-- url     : https://prove2.me/theorems/3f1c06f3-b993-49e1-84ff-dd7b3930254c
-- title:
--   First Passage Linear Transport: normalized multiplicative Hit Count ge
-- statement:
--   The First Passage Linear Transport construction uses the normalized multiplicative Hit Count ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3088-L3129
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3088-L3129

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.normalized_multiplicativeHitCount_ge
    {u eps : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r)
    (heps : 0 < eps) :
    (2 / (3 * u)) * (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r := by sorry
