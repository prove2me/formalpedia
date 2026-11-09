-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_pgFun_rotPoly
-- name    : BookProof.QuadraticRotation.pgFun_rotPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:30:37.424672+00:00
-- url     : https://prove2.me/theorems/1c8eea89-9d68-4ddb-acd1-ba290cfcbf45
-- title:
--   The Lean 4 theorem `pgFun_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFun_rotPoly` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.pgFun_rotPoly
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

theorem BookProof.QuadraticRotation.pgFun_rotPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (rotPoly O p) x = pgFun p (rotIso hO x) := by sorry
