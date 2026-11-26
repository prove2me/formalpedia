-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_orbit_le_start_power
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_start_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:29.466784+00:00
-- url     : https://prove2.me/theorems/a0972037-52bf-4d3d-99cc-15b0cec1dbf8
-- title:
--   Timeout Recertification Run: orbit le start power
-- statement:
--   Every prefix of a timeout run obeys the same outer power ceiling.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L76-L164
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L76-L164

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_start_power
    {P : TimeoutHighRunData} {K₀ beta : ℝ}
    {L M S n elapsed q : ℕ}
    (hbeta : 0 < beta) (htau : P.tau < beta)
    (hLowMargin : 2 * (S : ℝ) ≤ beta * (M : ℝ))
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by sorry
