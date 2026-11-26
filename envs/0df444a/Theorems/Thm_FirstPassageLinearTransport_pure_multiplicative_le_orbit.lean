-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_pure_multiplicative_le_orbit
-- name    : FirstPassageLinearTransport.pure_multiplicative_le_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:14.360626+00:00
-- url     : https://prove2.me/theorems/942f699e-ad33-4b0e-a087-5de5d359c38b
-- title:
--   First Passage Linear Transport: pure multiplicative le orbit
-- statement:
--   The pure multiplicative part of the affine Collatz iterate is a lower
--   bound for the actual shortcut state.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L132-L137
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L132-L137

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.pure_multiplicative_le_orbit (n j : ℕ) :
    ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) ≤
      (orbit j n : ℝ) := by sorry
