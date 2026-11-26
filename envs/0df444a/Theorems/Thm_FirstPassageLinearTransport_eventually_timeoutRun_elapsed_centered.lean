-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_elapsed_centered
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_elapsed_centered
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:29:31.055848+00:00
-- url     : https://prove2.me/theorems/6fe8cca9-7f22-5b89-b4ab-83f5c9be15ef
-- title:
--   First Passage Linear Transport: eventually timeout Run elapsed centered
-- statement:
--   Uniform two-sided drift estimate for the elapsed time of every timeout
--   run whose terminal rank is below the logarithmic switch.  This is the
--   centered-clock form of the same potential estimate used to count feasible
--   times.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L313-L380
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L313-L380

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_elapsed_centered
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      q ≤ shrinkingSwitchRank C M →
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      |driftGap * (elapsed : ℝ) - (M : ℝ)| ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
