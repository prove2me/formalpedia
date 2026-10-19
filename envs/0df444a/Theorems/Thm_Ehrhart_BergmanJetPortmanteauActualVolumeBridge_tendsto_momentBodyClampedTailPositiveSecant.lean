-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_tendsto_momentBodyClampedTailPositiveSecant
-- name    : Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_momentBodyClampedTailPositiveSecant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/93d9ed67-0e9c-4ba5-baad-5fb95bdf3501
-- title:
--   Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_momentBodyClampedTailPositiveSecant
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

theorem Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    Tendsto
      (fun r : ℕ =>
        momentBodyClampedTailPositiveSecant K p r t ht q)
      atTop
      (𝓝 (max 0 (momentBodyEnvelopePositiveSecant K p t q))) := by sorry
