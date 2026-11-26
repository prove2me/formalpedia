-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_binaryBarrierRate_endpoint_lipschitz
-- name    : FirstPassageLinearTransport.exists_binaryBarrierRate_endpoint_lipschitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:59.017103+00:00
-- url     : https://prove2.me/theorems/00a73296-b05a-561e-8c23-5c5438e1b48b
-- title:
--   First Passage Linear Transport: exists binary Barrier Rate endpoint lipschitz
-- statement:
--   The binary barrier rate is Lipschitz on the compact interval joining half
--   the endpoint displacement to the endpoint itself.  No numerical derivative
--   bound is needed; compactness supplies one fixed constant.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L40-L108
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L40-L108

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_binaryBarrierRate_endpoint_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
        ∀ y ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
          ‖binaryBarrierRate y - binaryBarrierRate x‖ ≤ C * ‖y - x‖ := by sorry
