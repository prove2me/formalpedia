-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
-- name    : FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:18.989796+00:00
-- url     : https://prove2.me/theorems/ff0df3be-e457-4076-b036-32b9ad189b7c
-- title:
--   First Passage Linear Transport: mem shrinking Feasible Times
-- statement:
--   The First Passage Linear Transport construction uses the mem shrinking Feasible Times property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L418-L430
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L418-L430

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
    {P : ShrinkingBarrierRunData} {M S q h : ℕ} :
    h ∈ shrinkingFeasibleTimes P M S q ↔
      h ≤ twoRegimeHorizon P.rHi P.rLo S M ∧
        ∃ n : ℕ, n ∈ dyadicShell M ∧
          ShrinkingRecertificationRun P M S n h q := by sorry
