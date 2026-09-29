-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_cpoly_gradPoly
-- name    : BookProof.SqSumFarisLavine.cpoly_gradPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:53:45.607318+00:00
-- url     : https://prove2.me/theorems/8041434d-59db-4fb7-bed9-039a9108d255
-- title:
--   (v : R → Fin D → ℝ) (k : Fin D) : cpoly (gradPoly v k) = gradPoly v k
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.cpoly_gradPoly` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.cpoly_gradPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.cpoly_gradPoly (v : R → Fin D → ℝ) (k : Fin D) :
    cpoly (gradPoly v k) = gradPoly v k := by sorry
