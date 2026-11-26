-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_shortcut_raw_le_relative_height
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.shortcut_raw_le_relative_height
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:13.90647+00:00
-- url     : https://prove2.me/theorems/749100d0-9cf8-5b14-9fcc-ee6123e6c385
-- title:
--   Timeout Recertification Run: shortcut raw le relative height
-- statement:
--   The preceding shortcut estimate and the exact raw/shortcut interleaving
--   give both relative-height ceilings through the same timeout-run endpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L287-L307
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L287-L307

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.shortcut_raw_le_relative_height
    {P : TimeoutHighRunData} {K₀ R : ℝ}
    {L M S n elapsed q : ℕ}
    (hR : 4 ≤ R)
    (hcontract : (P.rHi : ℝ) * (1 + P.tau) ≤ 1)
    (hLowMargin : 2 * S ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    (hnMax : n ∉ shellMultiplicativeHit M (R / 4)) :
    (∀ j : ℕ, j ≤ elapsed →
        (orbit j n : ℝ) ≤ (n : ℝ) * R / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n elapsed →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R) := by sorry
