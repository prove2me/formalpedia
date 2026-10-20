-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
-- name    : Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/3b31fb96-b6b3-4c54-9762-3610bd038c34
-- title:
--   Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
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
open Ehrhart.BergmanJetJointHolomorphicApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicApproximation.sourceJointCoverVolume_isAddHaar

theorem Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - w • y)) 0 1) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) := by sorry
