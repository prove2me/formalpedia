-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/66ee0cd7-e14d-41fe-bd1f-1ea3d4d1cae2
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
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
open Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative LogPartitionConvexity
open JointHolomorphicLaurentFourierCompatibility EnvelopeSmoothing EnvelopeGeneralTorusDescent
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph RadialSchurBlock TorusDeckGraphAdjoint
open RadialPhysicalInverseSquareRootEnergy MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicFullLeviSchur
open BergmanJetHolomorphicPhysicalMeasure BergmanJetHolomorphicPhysicalSupport
open BergmanJetJointHolomorphicPhysicalApproximation BergmanJetJointHolomorphicTimeDerivativeBounds
open TorusHomogeneousBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff

theorem Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t) ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by sorry
