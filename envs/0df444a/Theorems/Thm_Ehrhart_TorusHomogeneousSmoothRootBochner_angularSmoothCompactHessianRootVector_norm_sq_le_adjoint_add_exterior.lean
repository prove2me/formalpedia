-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
-- name    : Ehrhart.TorusHomogeneousSmoothRootBochner.angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/efd8a3e0-07c1-46d6-be39-831b5a5fbcc6
-- title:
--   Ehrhart.TorusHomogeneousSmoothRootBochner.angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
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
open Ehrhart.TorusHomogeneousSmoothRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.TorusHomogeneousSmoothRootBochner.angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    ‖(angularSmoothCompactHessianRootVector_memLp
      ha ha2 hH V hV hVp m).toLp
        (angularSmoothCompactHessianRootVector a V m)‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a (cutoffPhysicalField m V) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m V) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by sorry
