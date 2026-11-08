-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_pderiv_rotPoly
-- name    : BookProof.QuadraticRotation.pderiv_rotPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:28:16.129323+00:00
-- url     : https://prove2.me/theorems/e5ffedbe-ee27-4fb5-bb67-2775ba769895
-- title:
--   The Lean 4 theorem `pderiv_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.pderiv_rotPoly
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

theorem BookProof.QuadraticRotation.pderiv_rotPoly (O : Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    pderiv k (rotPoly O p) = ∑ i, C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p) := by sorry
