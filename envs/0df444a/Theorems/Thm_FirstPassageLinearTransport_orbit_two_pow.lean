-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_two_pow
-- name    : FirstPassageLinearTransport.orbit_two_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:11:02.922294+00:00
-- url     : https://prove2.me/theorems/63360467-8174-5309-be82-92b8a0c7ce89
-- title:
--   First Passage Linear Transport: orbit two pow
-- statement:
--   Shortcut iteration removes exactly one factor of two per step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L64-L76
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L64-L76

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.orbit_two_pow (q : ℕ) : orbit q (2 ^ q) = 1 := by sorry
