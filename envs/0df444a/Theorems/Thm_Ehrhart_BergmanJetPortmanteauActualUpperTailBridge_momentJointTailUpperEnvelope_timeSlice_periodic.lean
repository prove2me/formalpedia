-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_momentJointTailUpperEnvelope_timeSlice_periodic
-- name    : Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.momentJointTailUpperEnvelope_timeSlice_periodic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/894ad659-5fc8-4819-99cc-6a4c1fad90e3
-- title:
--   Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.momentJointTailUpperEnvelope_timeSlice_periodic
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

theorem Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.momentJointTailUpperEnvelope_timeSlice_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint z t ht))
      (imaginaryShift m) := by sorry
