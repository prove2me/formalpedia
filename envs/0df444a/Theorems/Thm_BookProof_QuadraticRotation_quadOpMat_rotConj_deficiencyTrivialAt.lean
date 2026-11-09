-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotConj_deficiencyTrivialAt
-- name    : BookProof.QuadraticRotation.quadOpMat_rotConj_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:30:26.330199+00:00
-- url     : https://prove2.me/theorems/f36e1650-fb41-4161-9b2c-870a17469b71
-- title:
--   The Lean 4 theorem `quadOpMat_rotConj_deficiencyTrivialAt` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOpMat_rotConj_deficiencyTrivialAt` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadOpMat_rotConj_deficiencyTrivialAt
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadOpMat_rotConj_deficiencyTrivialAt {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (c : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (quadOpMat (rotConj O c)) z := by sorry
