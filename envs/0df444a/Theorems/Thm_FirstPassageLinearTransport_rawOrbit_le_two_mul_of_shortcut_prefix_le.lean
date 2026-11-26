-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_le_two_mul_of_shortcut_prefix_le
-- name    : FirstPassageLinearTransport.rawOrbit_le_two_mul_of_shortcut_prefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:19:47.224804+00:00
-- url     : https://prove2.me/theorems/4ce628ca-d1a5-5fce-86bf-84dc9fa47982
-- title:
--   First Passage Linear Transport: raw Orbit le two mul of shortcut prefix le
-- statement:
--   Every raw iterate through a shortcut prefix is either a shortcut state or
--   the single doubled intermediate state following an odd shortcut source.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L278-L347
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L278-L347

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawOrbit_le_two_mul_of_shortcut_prefix_le
    {n k : ℕ} {C : ℝ}
    (hshortcut : ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ C) :
    ∀ i : ℕ, i ≤ rawTime n k → (rawOrbit i n : ℝ) ≤ 2 * C := by sorry
