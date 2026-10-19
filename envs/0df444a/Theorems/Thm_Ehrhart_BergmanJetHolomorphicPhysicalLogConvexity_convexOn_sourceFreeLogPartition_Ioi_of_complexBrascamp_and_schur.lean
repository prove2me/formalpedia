-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/caff67da-0e14-4285-b583-473c364a0ded
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
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

theorem Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
    {n : ℕ}
    (a f j E : ℝ → LogTorus n → ℝ)
    (ha : ∀ t : ℝ, Continuous (a t))
    (hf : ∀ t : ℝ, Continuous (f t))
    (hj : ∀ t : ℝ, Continuous (j t))
    (hderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => a u q) (f t q) t)
    (hfderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => f u q) (j t q) t)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ (t : ℝ), 0 < t → ∀ q : LogTorus n,
      sourceTimeDensity a t q ≤ M q)
    (hpart : ∀ (t : ℝ), 0 < t → 0 < sourcePartition a t)
    (hprob : ∀ (t : ℝ), 0 < t →
      IsProbabilityMeasure (sourceProbability a t))
    (hfbound : ∀ (t : ℝ), 0 < t → ∃ B : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ (t : ℝ), 0 < t → ∃ J : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |j u q| ≤ J)
    (hEint : ∀ (t : ℝ), 0 < t →
      Integrable (E t) (sourceProbability a t))
    (hcomplexBrascamp : ∀ (t : ℝ), 0 < t →
      sourceProbabilityVariance a t (f t) ≤
        sourceProbabilityMean a t (E t))
    (hschur : ∀ (t : ℝ), 0 < t →
      ∀ q : LogTorus n, E t q ≤ j t q) :
    ConvexOn ℝ (Set.Ioi 0) (sourceLogPartition a) := by sorry
