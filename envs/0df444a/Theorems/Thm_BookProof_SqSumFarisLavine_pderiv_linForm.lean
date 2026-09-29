-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_linForm
-- name    : BookProof.SqSumFarisLavine.pderiv_linForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:01.23787+00:00
-- url     : https://prove2.me/theorems/82dcbf1f-b242-4245-a688-9ff75c4e8e18
-- title:
--   (v : Fin D → ℝ) (j : Fin D) : pderiv j (linForm v) = C ((v j : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.pderiv_linForm` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.pderiv_linForm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.pderiv_linForm (v : Fin D → ℝ) (j : Fin D) :
    pderiv j (linForm v) = C ((v j : ℝ) : ℂ) := by sorry
