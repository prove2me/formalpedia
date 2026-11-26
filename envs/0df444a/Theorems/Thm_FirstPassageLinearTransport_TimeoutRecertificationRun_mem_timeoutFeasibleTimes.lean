-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_mem_timeoutFeasibleTimes
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.mem_timeoutFeasibleTimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:26:12.957298+00:00
-- url     : https://prove2.me/theorems/20479fcb-7f12-4f84-879a-d9e02c40e3a1
-- title:
--   Timeout Recertification Run: mem timeout Feasible Times
-- statement:
--   The Timeout Recertification Run construction uses the mem timeout Feasible Times property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L527-L552
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L527-L552

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.mem_timeoutFeasibleTimes
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hnShell : n ∈ dyadicShell M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    elapsed ∈ timeoutFeasibleTimes P K₀ L M S q := by sorry
