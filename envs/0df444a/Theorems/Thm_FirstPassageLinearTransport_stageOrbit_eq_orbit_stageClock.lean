-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageOrbit_eq_orbit_stageClock
-- name    : FirstPassageLinearTransport.stageOrbit_eq_orbit_stageClock
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:14:24.81728+00:00
-- url     : https://prove2.me/theorems/aa194e97-bb8f-45a8-b79b-b8b0f9c60551
-- title:
--   First Passage Linear Transport: stage Orbit eq orbit stage Clock
-- statement:
--   Concatenating stopped blocks is an exact shortcut iterate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L231-L238
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L231-L238

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageOrbit_eq_orbit_stageClock {r eta : ℝ}
    (p : StageSetup r eta) (R n : ℕ) :
    stageOrbit p R n = orbit (stageClock p R n) n := by sorry
