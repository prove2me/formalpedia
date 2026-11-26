-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_completed_centered
-- name    : FirstPassageLinearTransport.eventually_timeoutRun_completed_centered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:39.063963+00:00
-- url     : https://prove2.me/theorems/a73085e6-af74-45bc-9410-b9c4dba872d6
-- title:
--   First Passage Linear Transport: eventually timeout Run completed centered
-- statement:
--   The same centered estimate after completing a dyadic terminal endpoint by
--   exact halving.  When `q ≤ L` the completion length `q - L` is zero.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L384-L449
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L384-L449

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutRun_completed_centered
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      q ≤ shrinkingSwitchRank C M →
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      |driftGap * ((elapsed + (q - L) : ℕ) : ℝ) - (M : ℝ)| ≤
        2 * timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
