-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicApproximation_momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
-- name    : Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/7b0df764-2adb-42e2-9dfa-97396d112d18
-- title:
--   Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
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

theorem Ehrhart.BergmanJetJointHolomorphicApproximation.momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope K F htransport p q ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k q := by sorry
