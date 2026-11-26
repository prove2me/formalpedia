-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_affineCorrection_lt_two_pow_mul_three_pow
-- name    : FirstPassageLinearTransport.affineCorrection_lt_two_pow_mul_three_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:25:10.53864+00:00
-- url     : https://prove2.me/theorems/3e86c87c-5e03-4fad-917b-053def1c1a5c
-- title:
--   First Passage Linear Transport: affine Correction lt two pow mul three pow
-- statement:
--   The affine correction is strictly smaller than one full geometric copy
--   of the multiplicative term.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L89-L127
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L89-L127

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology

theorem FirstPassageLinearTransport.affineCorrection_lt_two_pow_mul_three_pow (n k : ℕ) :
    affineCorrection n k < 2 ^ k * 3 ^ oddCount n k := by sorry
