-- Prove2me | Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularCurvatureDensity_re_eq_squareRoot_norm_sq
-- name    : Ehrhart.TorusHomogeneousSmoothRootBochner.angularCurvatureDensity_re_eq_squareRoot_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/32026660-7016-4538-8cda-26ef0045eb2d
-- title:
--   Ehrhart.TorusHomogeneousSmoothRootBochner.angularCurvatureDensity_re_eq_squareRoot_norm_sq
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

theorem Ehrhart.TorusHomogeneousSmoothRootBochner.angularCurvatureDensity_re_eq_squareRoot_norm_sq
    {n : ℕ} {a : LogTorus n → ℝ}
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    (angularTorusFormCurvatureDensity a V q).re =
      ‖Matrix.toEuclideanLin
        (angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q)
        (angularTorusConjugatePhysicalFormVector V q)‖ ^ 2 := by sorry
