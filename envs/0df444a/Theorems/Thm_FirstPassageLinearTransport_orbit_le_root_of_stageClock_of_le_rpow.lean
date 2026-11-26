-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_le_root_of_stageClock_of_le_rpow
-- name    : FirstPassageLinearTransport.orbit_le_root_of_stageClock_of_le_rpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:00.412121+00:00
-- url     : https://prove2.me/theorems/2a6a4b9d-2464-4300-b25b-b45190c6c449
-- title:
--   First Passage Linear Transport: orbit le root of stage Clock of le rpow
-- statement:
--   Once a checkpoint lies below `root^r`, every prefix in the remaining
--   bootstrap chain stays below `root`, provided `r(1+eta) ≤ 1`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L79-L133
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L79-L133

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.orbit_le_root_of_stageClock_of_le_rpow
    {r eta : ℝ} (p : StageSetup r eta)
    (hre : r * (1 + eta) ≤ 1)
    {R m : ℕ} {root : ℝ}
    (hm : 0 < m) (hmSet : m ∈ bootstrapSet p R)
    (hroot : 1 ≤ root) (hmroot : (m : ℝ) ≤ root ^ r) :
    ∀ j : ℕ, j ≤ stageClock p R m → (orbit j m : ℝ) ≤ root := by sorry
