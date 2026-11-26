-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutFeasibleTimes_card_le_potential
-- name    : FirstPassageLinearTransport.timeoutFeasibleTimes_card_le_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:51.276844+00:00
-- url     : https://prove2.me/theorems/864437d9-5990-4436-9c42-a847a6a2390a
-- title:
--   First Passage Linear Transport: timeout Feasible Times card le potential
-- statement:
--   Exact cardinality bound for the feasible timeout times.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L555-L606
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L555-L606

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutFeasibleTimes_card_le_potential
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S q : ℕ} (hM : 1 ≤ M) :
    (timeoutFeasibleTimes P K₀ L M S q).card ≤
      ⌈(1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap)⌉₊ := by sorry
