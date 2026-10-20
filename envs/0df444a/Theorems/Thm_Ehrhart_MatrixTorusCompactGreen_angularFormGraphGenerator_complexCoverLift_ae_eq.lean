-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusCompactGreen_angularFormGraphGenerator_complexCoverLift_ae_eq
-- name    : Ehrhart.MatrixTorusCompactGreen.angularFormGraphGenerator_complexCoverLift_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/13c406a5-7343-4939-ab9b-3b66cf9268ec
-- title:
--   Ehrhart.MatrixTorusCompactGreen.angularFormGraphGenerator_complexCoverLift_ae_eq
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
open Ehrhart.MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff

theorem Ehrhart.MatrixTorusCompactGreen.angularFormGraphGenerator_complexCoverLift_ae_eq
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (F : LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) (j : Fin n) :
    complexTorusCoverLift
      (fun q : LogTorus n =>
        (angularBarPartialL2OfRepresentative a F hD q :
          EuclideanSpace ℂ (Fin n)) j)
        =ᵐ[(volume : Measure (LogSpace n))]
      (fun z => barPartialCoordinate F z j) := by sorry
