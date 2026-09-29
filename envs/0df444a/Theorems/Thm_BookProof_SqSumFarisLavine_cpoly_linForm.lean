-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_cpoly_linForm
-- name    : BookProof.SqSumFarisLavine.cpoly_linForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:08.297953+00:00
-- url     : https://prove2.me/theorems/0ae84b9b-84eb-44da-9917-c03bb2652a10
-- title:
--   (v : Fin D → ℝ) : cpoly (linForm v) = linForm v
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.cpoly_linForm` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.cpoly_linForm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.cpoly_linForm (v : Fin D → ℝ) : cpoly (linForm v) = linForm v := by sorry
