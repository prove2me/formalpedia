-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_orbit_le_half_relative_height
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_half_relative_height
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:33.470859+00:00
-- url     : https://prove2.me/theorems/14c60c24-51cc-41a5-a606-e7a72aa364f0
-- title:
--   Timeout Recertification Run: orbit le half relative height
-- statement:
--   Outside the exact initial multiplicative-maximum event, the first block
--   stays below `nR/2`.  The contraction condition keeps every later certified
--   high block below `n`, while the low switch margin does the same for literal
--   timeout blocks.  Thus the complete shortcut run retains the half-height
--   slack needed for raw-map conversion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L171-L283
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L171-L283

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.orbit_le_half_relative_height
    {P : TimeoutHighRunData} {K₀ R : ℝ}
    {L M S n elapsed q : ℕ}
    (hR : 4 ≤ R)
    (hcontract : (P.rHi : ℝ) * (1 + P.tau) ≤ 1)
    (hLowMargin : 2 * S ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    (hnMax : n ∉ shellMultiplicativeHit M (R / 4))
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) * R / 2 := by sorry
