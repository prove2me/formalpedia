-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
-- name    : FirstPassageLinearTransport.eventually_timeoutTimePotential_source_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:18:14.143582+00:00
-- url     : https://prove2.me/theorems/a46a0af8-c177-45be-847c-c41eae0cdddf
-- title:
--   First Passage Linear Transport: eventually timeout Time Potential source le sqrt
-- statement:
--   The high corridor plus the crude `S²` timeout reserve has the same
--   square-root-logarithmic scale as the frozen feasible-time support.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L673-L778
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L673-L778

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutTimePotential_source_le_sqrt
    (P : TimeoutHighRunData) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
