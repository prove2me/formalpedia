-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
-- name    : Ehrhart.TorusHomogeneousCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/b7e58f65-4ffe-4dba-b3e5-1cabd22712a7
-- title:
--   Ehrhart.TorusHomogeneousCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
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
open Ehrhart.TorusHomogeneousCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusFriedrichsMollifierEstimates TorusWeightedAdjointMollification
open TorusStrongWeightedTorusDescent TorusStrongWeightedRadialCutoff TorusFriedrichsCutoff
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusHomogeneousCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun ℓ : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by sorry
