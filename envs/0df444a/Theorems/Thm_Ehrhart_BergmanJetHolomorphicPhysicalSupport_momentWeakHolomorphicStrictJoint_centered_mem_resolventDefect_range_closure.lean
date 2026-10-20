-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalSupport_momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/8f76f066-49a3-470a-b7eb-185927c796e1
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
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
open Ehrhart.BergmanJetHolomorphicPhysicalSupport
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution

theorem Ehrhart.BergmanJetHolomorphicPhysicalSupport.momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (f : angularWeightedScalarL2
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t))
    (hf :
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t))) = 0) :
    f ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by sorry
