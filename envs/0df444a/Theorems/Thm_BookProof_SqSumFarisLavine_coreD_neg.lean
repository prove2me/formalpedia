-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_coreD_neg
-- name    : BookProof.SqSumFarisLavine.coreD_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:47:17.997847+00:00
-- url     : https://prove2.me/theorems/29c2b8ef-7489-4b08-afd6-4e2c53efb3d8
-- title:
--   (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (-p) = -coreD j p
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.coreD_neg` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.coreD_neg
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.coreD_neg (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (-p) = -coreD j p := by sorry
