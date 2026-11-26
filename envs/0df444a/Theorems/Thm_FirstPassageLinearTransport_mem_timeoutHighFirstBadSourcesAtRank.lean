-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
-- name    : FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:43.878055+00:00
-- url     : https://prove2.me/theorems/7fc069c6-13eb-42e8-ab91-a4489bb5beed
-- title:
--   First Passage Linear Transport: mem timeout High First Bad Sources At Rank
-- statement:
--   The First Passage Linear Transport construction uses the mem timeout High First Bad Sources At Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L37-L45
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L37-L45

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S q n : ℕ} :
    n ∈ timeoutHighFirstBadSourcesAtRank P K₀ L M S q ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h q ∧
          orbit h n ∈ landingBad q (timeoutHighTargetTolerance P M q) := by sorry
