-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_gaussInt_rotPoly
-- name    : BookProof.QuadraticRotation.gaussInt_rotPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:30:34.237817+00:00
-- url     : https://prove2.me/theorems/96a9b7d7-362b-40c1-b55d-4985e138b5fa
-- title:
--   The Lean 4 theorem `gaussInt_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.gaussInt_rotPoly
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

theorem BookProof.QuadraticRotation.gaussInt_rotPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (r : MvPolynomial (Fin d) ℂ) : gaussInt (rotPoly O r) = gaussInt r := by sorry
