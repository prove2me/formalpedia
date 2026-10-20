-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_sourceFreeWeightedObservable_integrable_of_majorant
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeWeightedObservable_integrable_of_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/4a190d7d-4b1e-47e8-bc49-be1d4df13de6
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeWeightedObservable_integrable_of_majorant
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

theorem Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.sourceFreeWeightedObservable_integrable_of_majorant
    {n : ℕ}
    (a : ℝ → LogTorus n → ℝ)
    (F : LogTorus n → ℝ) (t B : ℝ)
    (ha : Continuous (a t)) (hF : Continuous F)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ q : LogTorus n, sourceTimeDensity a t q ≤ M q)
    (hbound : ∀ q : LogTorus n, |F q| ≤ B) :
    Integrable (fun q => F q * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) := by sorry
