-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_deviation_add_potential_le
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.deviation_add_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:19:15.926638+00:00
-- url     : https://prove2.me/theorems/b837218d-9474-5678-8469-b6dfea48b3fc
-- title:
--   Timeout Recertification Run: deviation add potential le
-- statement:
--   Every timeout run lies in one common interval around the linear-drift
--   center `(M+1)-q`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L309-L510
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L309-L510

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.deviation_add_potential_le
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (M + 1) := by sorry
