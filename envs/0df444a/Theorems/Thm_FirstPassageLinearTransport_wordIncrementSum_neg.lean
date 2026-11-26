-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_neg
-- name    : FirstPassageLinearTransport.wordIncrementSum_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:58.809466+00:00
-- url     : https://prove2.me/theorems/7d2ed4a2-76c5-595e-8ebe-9f98d81e51b0
-- title:
--   First Passage Linear Transport: word Increment Sum neg
-- statement:
--   The First Passage Linear Transport construction uses the word Increment Sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L923-L927
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L923-L927

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.wordIncrementSum_neg
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum (fun bit ↦ -x bit) v = -wordIncrementSum x v := by sorry
