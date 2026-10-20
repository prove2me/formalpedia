-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodySharpJetScale_le_dimension_of_weakProbability
-- name    : Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodySharpJetScale_le_dimension_of_weakProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/caf4eec7-5bea-4d46-a7e5-d73b2e3898bd
-- title:
--   Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodySharpJetScale_le_dimension_of_weakProbability
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualVolumeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodySharpJetScale_le_dimension_of_weakProbability
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K (0 : LogSpace n)))) :
    (n : ℝ) * BodyScale.canonicalScale K /
      ((n : ℝ) + 1) ≤ (n : ℝ) := by sorry
