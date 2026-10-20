-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_continuous_sourcePositiveJointTimePoint_fixed
-- name    : Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.continuous_sourcePositiveJointTimePoint_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/e9fa7a5a-83e1-4781-84fa-0fc7ca4ff785
-- title:
--   Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.continuous_sourcePositiveJointTimePoint_fixed
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
open Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.continuous_sourcePositiveJointTimePoint_fixed
    {n : ℕ} (t : ℝ) (ht : 0 < t) :
    Continuous
      (fun z : LogSpace n => sourcePositiveJointTimePoint z t ht) := by sorry
