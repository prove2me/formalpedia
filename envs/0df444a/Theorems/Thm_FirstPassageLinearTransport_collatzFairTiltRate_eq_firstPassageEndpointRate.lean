-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzFairTiltRate_eq_firstPassageEndpointRate
-- name    : FirstPassageLinearTransport.collatzFairTiltRate_eq_firstPassageEndpointRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:01.661922+00:00
-- url     : https://prove2.me/theorems/45a2261d-9614-4845-8a8e-aea4db5f76a7
-- title:
--   First Passage Linear Transport: collatz Fair Tilt Rate eq first Passage Endpoint Rate
-- statement:
--   The finite-word change-of-measure rate is exactly the endpoint entropy
--   rate already used by the first-passage parameter layer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L839-L843
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L839-L843

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.collatzFairTiltRate_eq_firstPassageEndpointRate :
    collatzFairTiltRate = firstPassageEndpointRate := by sorry
