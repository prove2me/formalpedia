-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
-- name    : Ehrhart.TorusHomogeneousFriedrichs.angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/7d8a6693-4676-49a9-b517-e28b8e69b505
-- title:
--   Ehrhart.TorusHomogeneousFriedrichs.angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
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
open Ehrhart.TorusHomogeneousFriedrichs
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusDolbeault
open TorusWeightedBaseAE TorusWeakDolbeaultMollification TorusStrongCoverMollificationDensity
open TorusStrongWeightedTorusDescent TorusFriedrichsMollifierEstimates
open TorusWeightedAdjointMollification BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusHomogeneousFriedrichs.angularWeightedScalar_normalizedCoverMollification_compact_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n => f r)) k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by sorry
