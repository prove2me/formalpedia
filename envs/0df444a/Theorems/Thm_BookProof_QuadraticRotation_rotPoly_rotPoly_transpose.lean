-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_rotPoly_rotPoly_transpose
-- name    : BookProof.QuadraticRotation.rotPoly_rotPoly_transpose
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:28:43.522833+00:00
-- url     : https://prove2.me/theorems/4a94f721-079e-46a3-9b47-effc499c22d1
-- title:
--   The Lean 4 theorem `rotPoly_rotPoly_transpose` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rotPoly_rotPoly_transpose` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotPoly_rotPoly_transpose
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.rotPoly_rotPoly_transpose {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) : rotPoly O (rotPoly Oᵀ p) = p := by sorry
