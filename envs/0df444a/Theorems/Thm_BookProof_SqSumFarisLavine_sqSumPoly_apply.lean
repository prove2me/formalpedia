-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_sqSumPoly_apply
-- name    : BookProof.SqSumFarisLavine.sqSumPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:49:17.712277+00:00
-- url     : https://prove2.me/theorems/07b35b0a-8c2d-487d-a311-e2c9c070375b
-- title:
--   (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) : sqSumPoly kappa v p = kinPart kappa p + potPoly v * p
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.sqSumPoly_apply` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.sqSumPoly_apply
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.sqSumPoly_apply (kappa : Fin D → ℝ) (v : R → Fin D → ℝ)
    (p : MvPolynomial (Fin D) ℂ) :
    sqSumPoly kappa v p = kinPart kappa p + potPoly v * p := by sorry
