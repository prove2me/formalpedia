-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhysicalApproximation_momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
-- name    : Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/40053d5b-b9ad-4bfe-8ab6-638b8c684b2b
-- title:
--   Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
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
open Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger BergmanJetTorusEnvelope
open BergmanJetTorusCoercivity BergmanJetStrictRadialRegularizer
open BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open BergmanJetJointHolomorphicApproximation BergmanJetHolomorphicPhysicalMeasure
open JetEnvelopeRightDerivative JetEnvelopeSlopeConvergence JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSmoothing EnvelopeGeneralTorusDescent LogPartitionConvexity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder

theorem Ehrhart.BergmanJetJointHolomorphicPhysicalApproximation.momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (q : LogTorus n) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k
          (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by sorry
