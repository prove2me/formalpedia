-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_integral_comp_rotIso
-- name    : BookProof.QuadraticRotation.integral_comp_rotIso
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:24:47.835444+00:00
-- url     : https://prove2.me/theorems/36e91c3a-f653-4433-be16-0f75eed9fe11
-- title:
--   The Lean 4 theorem `integral_comp_rotIso` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integral_comp_rotIso` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.integral_comp_rotIso
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.integral_comp_rotIso {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (g : Vd d → ℂ) : ∫ x : Vd d, g (rotIso hO x) = ∫ y : Vd d, g y := by sorry
