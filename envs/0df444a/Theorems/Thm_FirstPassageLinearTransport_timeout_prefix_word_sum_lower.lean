-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_prefix_word_sum_lower
-- name    : FirstPassageLinearTransport.timeout_prefix_word_sum_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:39:19.324656+00:00
-- url     : https://prove2.me/theorems/2f463c28-d108-4637-ae3c-612f6b339326
-- title:
--   First Passage Linear Transport: timeout prefix word sum lower
-- statement:
--   Every prefix of a literal timeout word stays above the exact logarithmic
--   barrier supplied by the parent and target ranks.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L71-L126
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L71-L126

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeout_prefix_word_sum_lower
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m)
    (j : Fin (m + 1)) :
    -(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2) <
      wordIncrementSum collatzLogIncrement (boolParityWord j x) := by sorry
