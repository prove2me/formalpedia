-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousRadialMatrix_angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
-- name    : Ehrhart.TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/56e34dd3-b64a-4a3e-9a10-35ceac3a51ca
-- title:
--   Ehrhart.TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
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
open Ehrhart.TorusHomogeneousRadialMatrix
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B) :
    ‖angularClosedMollifiedRadialMatrixCommutatorL2 ha W ℓ m -
      (angularWeakSourceCutoffDerivativeCommutator_memLp
        W hB m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2 ≤
      (((m : ℝ) + 1)⁻¹ * B) ^ 2 *
        (∫ q in tsupport (sourceCutoffBarGradient (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by sorry
