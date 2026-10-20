-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeScalarCutoffGradient_L2_norm_le
-- name    : Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarCutoffGradient_L2_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:08.235634+00:00
-- url     : https://prove2.me/theorems/273cda6e-2adc-480f-8cb6-e2331890ef7b
-- title:
--   Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarCutoffGradient_L2_norm_le
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
open Ehrhart.TorusHomogeneousBrascampLieb
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff

theorem Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarCutoffGradient_L2_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    {C : ℝ} (hCnonneg : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m).toLp
      (angularSourceFreeScalarCutoffGradient U m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) *
        ‖hu.toLp (torusScalarRepresentative U)‖ := by sorry
