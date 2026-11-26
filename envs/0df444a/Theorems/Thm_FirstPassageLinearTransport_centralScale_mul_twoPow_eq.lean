-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_centralScale_mul_twoPow_eq
-- name    : FirstPassageLinearTransport.centralScale_mul_twoPow_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:11:10.368465+00:00
-- url     : https://prove2.me/theorems/7d8b0904-19a5-469f-989c-d56ca9392f48
-- title:
--   First Passage Linear Transport: central Scale mul two Pow eq
-- statement:
--   The central scale at a power-of-two source is the exact exponent used in
--   the power-of-two exclusion argument.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L80-L90
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean#L80-L90

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.centralScale_mul_twoPow_eq
    (q : ℕ) (t : ℝ) :
    centralOrbitScale q * (((2 ^ q : ℕ) : ℝ) ^ (1 - t)) =
      (2 : ℝ) ^ ((a0 - t) * (q : ℝ)) := by sorry
