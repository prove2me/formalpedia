-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_sharpMovingRankBuffer_const_le
-- name    : FirstPassageLinearTransport.two_rpow_neg_sharpMovingRankBuffer_const_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:53:32.976461+00:00
-- url     : https://prove2.me/theorems/3011b25e-e9b3-54ad-bf3c-ae72f7234863
-- title:
--   First Passage Linear Transport: two rpow neg sharp Moving Rank Buffer const le
-- statement:
--   The sharp timeout term at a fixed exponent is bounded by the exact
--   negative power dictated by the endpoint margin.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L459-L483
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L459-L483

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_rpow_neg_sharpMovingRankBuffer_const_le
    {A : ℝ} (_hA : timeSupportCriticalExponent < A) (M : ℕ) :
    (2 : ℝ) ^ (-(sharpMovingRankBuffer (fun _ => A) M)) ≤
      (((M : ℝ) + 2) ^ (-(fixedSharpEndpointMargin A))) := by sorry
