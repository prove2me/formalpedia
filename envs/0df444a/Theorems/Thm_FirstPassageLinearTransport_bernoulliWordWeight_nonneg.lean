-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
-- name    : FirstPassageLinearTransport.bernoulliWordWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:51.050017+00:00
-- url     : https://prove2.me/theorems/70cfbe33-3b3f-4c27-b845-69041ea686f1
-- title:
--   First Passage Linear Transport: bernoulli Word Weight nonneg
-- statement:
--   The First Passage Linear Transport construction uses the bernoulli Word Weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1162-L1167
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1162-L1167

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliWordWeight_nonneg
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {r : ℕ} (v : Fin r → Bool) :
    0 ≤ bernoulliWordWeight p v := by sorry
