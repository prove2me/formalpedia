-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicTimeDerivativeBounds_upperRegularization_sourceJointCover_translate_le
-- name    : Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.upperRegularization_sourceJointCover_translate_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/cce9b6cc-3d53-4553-a498-bf94117d7fd4
-- title:
--   Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.upperRegularization_sourceJointCover_translate_le
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
open Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.sourceJointCoverVolume_isAddHaar

theorem Ehrhart.BergmanJetJointHolomorphicTimeDerivativeBounds.upperRegularization_sourceJointCover_translate_le
    {n : ℕ} (f : SourceJointComplexCover n → ℝ)
    (hlocal : ∀ q : SourceJointComplexCover n,
      (localUpperBounds f q).Nonempty)
    (d : SourceJointComplexCover n) (C : ℝ)
    (hshift : ∀ q : SourceJointComplexCover n,
      f (q + d) ≤ f q + C)
    (q : SourceJointComplexCover n) :
    upperRegularization f (q + d) ≤
      upperRegularization f q + C := by sorry
