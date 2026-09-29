-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_pderiv_harmPoly
-- name    : BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:05:10.676803+00:00
-- url     : https://prove2.me/theorems/b86fbc9f-6d29-46e2-aeb2-c894b40eedc3
-- title:
--   (j : Fin D) : pderiv j (pderiv j (harmPoly (d
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.pderiv_pderiv_harmPoly (j : Fin D) :
    pderiv j (pderiv j (harmPoly (d := D))) = C (1 / 2 : ℂ) := by sorry
