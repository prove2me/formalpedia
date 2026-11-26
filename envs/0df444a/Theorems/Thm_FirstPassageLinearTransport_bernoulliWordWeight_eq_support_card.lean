-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_eq_support_card
-- name    : FirstPassageLinearTransport.bernoulliWordWeight_eq_support_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:30.823801+00:00
-- url     : https://prove2.me/theorems/617fd747-8ae7-54c8-81a4-a90560472031
-- title:
--   First Passage Linear Transport: bernoulli Word Weight eq support card
-- statement:
--   The First Passage Linear Transport construction uses the bernoulli Word Weight eq support card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1447-L1469
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1447-L1469

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.bernoulliWordWeight_eq_support_card
    {p : ℝ} {r : ℕ} (v : Fin r → Bool) :
    bernoulliWordWeight p v =
      p ^ (boolSupport v).card *
        (1 - p) ^ (r - (boolSupport v).card) := by sorry
