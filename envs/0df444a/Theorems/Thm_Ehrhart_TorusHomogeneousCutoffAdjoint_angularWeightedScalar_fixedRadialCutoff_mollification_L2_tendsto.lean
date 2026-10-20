-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
-- name    : Ehrhart.TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/9a0ec6f4-b9f0-485c-98d9-c0b9409080d5
-- title:
--   Ehrhart.TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
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

theorem Ehrhart.TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a) (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (angularWeightedScalar_fixedRadialCutoff_mollification_memLp
          ha f m k).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => f r)) k) q))
      atTop
      (nhds
        ((angularSourceRadialCutoff_smul_memLp
          (MeasureTheory.Lp.memLp f) m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • f q))) := by sorry
