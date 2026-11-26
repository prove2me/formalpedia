-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_word_survives_exact_barrier
-- name    : FirstPassageLinearTransport.timeout_word_survives_exact_barrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:48.216527+00:00
-- url     : https://prove2.me/theorems/192f576f-b641-4504-aa8f-b2653765bc7a
-- title:
--   First Passage Linear Transport: timeout word survives exact barrier
-- statement:
--   Literal timeout containment in an exact finite-word barrier language.
--   The following uniform low-rank theorem replaces this rank-dependent barrier
--   by the fixed constant used in Lemma 6.3.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L131-L142
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L131-L142

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeout_word_survives_exact_barrier
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    wordSurvivesFrom
      (-(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2))
      collatzLogIncrement m 0 (boolParityWord m x) := by sorry
