-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_prefix_log_deviation_add_potential_le
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.prefix_log_deviation_add_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:08.774462+00:00
-- url     : https://prove2.me/theorems/9e250a7d-4e4b-550c-a3b3-68fc9c25ce2b
-- title:
--   Timeout Recertification Run: prefix log deviation add potential le
-- statement:
--   Every shortcut prefix of a mixed timeout run stays in one common
--   square-root-logarithmic tube.  The factor two lets the same potential pay the
--   coarse low-block estimate `|deviation| ≤ 2 duration`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L823-L935
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L823-L935

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.prefix_log_deviation_add_potential_le
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    ∀ j : ℕ, j ≤ elapsed →
      |shortcutLogDeviation n j| + 2 * timeoutTimePotential P M S q ≤
        2 * timeoutTimePotential P M S (M + 1) := by sorry
