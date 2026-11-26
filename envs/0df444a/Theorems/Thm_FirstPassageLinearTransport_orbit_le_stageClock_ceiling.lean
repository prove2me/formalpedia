-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_le_stageClock_ceiling
-- name    : FirstPassageLinearTransport.orbit_le_stageClock_ceiling
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:57.997218+00:00
-- url     : https://prove2.me/theorems/6f5ad542-27ab-4360-bd7d-5c506681f57d
-- title:
--   First Passage Linear Transport: orbit le stage Clock ceiling
-- statement:
--   Coarse all-prefix bootstrap envelope.  It deliberately keeps the
--   startup loss as `stageK^(2R)`; this becomes only polynomial on the scheduled
--   depth and is absorbed below.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L441-L495
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L441-L495

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.orbit_le_stageClock_ceiling
    {r eta : ℝ} (p : StageSetup r eta) {R n j : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R)
    (hj : j ≤ stageClock p R n) :
    (orbit j n : ℝ) ≤
      stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := by sorry
