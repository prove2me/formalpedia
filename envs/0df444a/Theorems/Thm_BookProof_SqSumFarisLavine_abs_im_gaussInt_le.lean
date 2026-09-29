-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_abs_im_gaussInt_le
-- name    : BookProof.SqSumFarisLavine.abs_im_gaussInt_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:47:10.467979+00:00
-- url     : https://prove2.me/theorems/b7933587-4afe-471a-aba0-398fad74fb96
-- title:
--   (q w : MvPolynomial (Fin D) ℂ) : |(gaussInt (cpoly q * w)).im| ≤ ‖pgLp q‖ * ‖pgLp w‖
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.abs_im_gaussInt_le` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.abs_im_gaussInt_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.abs_im_gaussInt_le (q w : MvPolynomial (Fin D) ℂ) :
    |(gaussInt (cpoly q * w)).im| ≤ ‖pgLp q‖ * ‖pgLp w‖ := by sorry
