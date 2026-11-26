-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_eq_entropyGap_mul_logTwo
-- name    : FirstPassageLinearTransport.firstPassageEndpointRate_eq_entropyGap_mul_logTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:16:54.577444+00:00
-- url     : https://prove2.me/theorems/d5a0d8b3-17a2-4833-95fc-4c21b4db2fde
-- title:
--   First Passage Linear Transport: first Passage Endpoint Rate eq entropy Gap mul log Two
-- statement:
--   The natural-log endpoint rate is the base-two entropy gap multiplied by
--   `log 2`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L46-L52
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L46-L52

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.firstPassageEndpointRate_eq_entropyGap_mul_logTwo :
    firstPassageEndpointRate = firstPassageEntropyGap * Real.log 2 := by sorry
