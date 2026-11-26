-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
-- name    : FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:24.999696+00:00
-- url     : https://prove2.me/theorems/79d6e780-7d65-4e12-8304-689d03420857
-- title:
--   First Passage Linear Transport: mem shrinking First Bad Sources At Rank
-- statement:
--   The First Passage Linear Transport construction uses the mem shrinking First Bad Sources At Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L39-L46
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L39-L46

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
    {P : ShrinkingBarrierRunData} {M S q n : ℕ} :
    n ∈ shrinkingFirstBadSourcesAtRank P M S q ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, ShrinkingRecertificationRun P M S n h q ∧
          orbit h n ∈ landingBad q (shrinkingTargetTolerance P M S q) := by sorry
