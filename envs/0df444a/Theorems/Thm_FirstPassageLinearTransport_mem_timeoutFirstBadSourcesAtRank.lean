-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
-- name    : FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:19:07.764669+00:00
-- url     : https://prove2.me/theorems/070c67b5-02f4-4a7a-a2b4-3c1a9da9f1b3
-- title:
--   First Passage Linear Transport: mem timeout First Bad Sources At Rank
-- statement:
--   The First Passage Linear Transport construction uses the mem timeout First Bad Sources At Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L74-L82
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L74-L82

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S p n : ℕ} :
    n ∈ timeoutFirstBadSourcesAtRank P K₀ L M S p ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h p ∧
          LowStageTimeout K₀ L (p - 1) (orbit h n) := by sorry
