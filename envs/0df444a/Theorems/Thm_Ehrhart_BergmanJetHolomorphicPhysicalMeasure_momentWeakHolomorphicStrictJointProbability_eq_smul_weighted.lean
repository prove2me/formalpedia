-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalMeasure_momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/e1138908-ee53-48a0-99a1-b980afa5dfee
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
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
open Ehrhart.BergmanJetHolomorphicPhysicalMeasure
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence MatrixTorusBochnerBridge
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger
open BergmanJetEnvelopePlurisubharmonic BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier EnvelopeSmoothing
open EnvelopeGeneralTorusDescent RadialPartitionBounds LogPartitionConvexity WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution

theorem Ehrhart.BergmanJetHolomorphicPhysicalMeasure.momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    sourceProbability
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t =
      (ENNReal.ofReal
        (sourcePartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t))⁻¹ •
        angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t) := by sorry
