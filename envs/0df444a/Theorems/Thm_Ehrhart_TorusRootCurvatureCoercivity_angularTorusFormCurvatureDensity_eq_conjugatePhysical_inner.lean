-- Prove2me | Theorems.Thm_Ehrhart_TorusRootCurvatureCoercivity_angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
-- name    : Ehrhart.TorusRootCurvatureCoercivity.angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:04.613882+00:00
-- url     : https://prove2.me/theorems/0ea4d22d-6b8a-47ed-b971-ffc666dd3ab3
-- title:
--   Ehrhart.TorusRootCurvatureCoercivity.angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
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
open Ehrhart.TorusRootCurvatureCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert ComplexKillingSaturationBridge WeightedTorusBochner
open WeightedTorusBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

theorem Ehrhart.TorusRootCurvatureCoercivity.angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
    {n : ℕ} (a : LogTorus n → ℝ)
    (W : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    angularTorusFormCurvatureDensity a W q =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (angularTorusConjugatePhysicalFormVector W q)
        (Matrix.toEuclideanLin
          (angularTorusComplexHessianMatrix a q)
          (angularTorusConjugatePhysicalFormVector W q)) := by sorry
