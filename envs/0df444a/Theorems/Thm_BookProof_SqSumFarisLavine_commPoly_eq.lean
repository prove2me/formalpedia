-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_commPoly_eq
-- name    : BookProof.SqSumFarisLavine.commPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:37.855503+00:00
-- url     : https://prove2.me/theorems/d6bc1db6-543b-46d7-8b58-41a2d86679db
-- title:
--   (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) : commPoly kappa v p = ((commConst kappa v : ℝ) : ℂ) • p + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ)...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.commPoly_eq` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.commPoly_eq
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.commPoly_eq (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commPoly kappa v p
      = ((commConst kappa v : ℝ) : ℂ) • p
        + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • (X j * coreD j p))
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by sorry
