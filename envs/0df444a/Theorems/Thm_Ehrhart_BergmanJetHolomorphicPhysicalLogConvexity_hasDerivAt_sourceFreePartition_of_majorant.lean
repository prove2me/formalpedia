-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetHolomorphicPhysicalLogConvexity_hasDerivAt_sourceFreePartition_of_majorant
-- name    : Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreePartition_of_majorant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/e51ff644-05f8-42fd-9c34-dfd965a2930d
-- title:
--   Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreePartition_of_majorant
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

theorem Ehrhart.BergmanJetHolomorphicPhysicalLogConvexity.hasDerivAt_sourceFreePartition_of_majorant
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B) :
    HasDerivAt (sourcePartition a)
      (-sourceFirstMoment a f t) t := by sorry
