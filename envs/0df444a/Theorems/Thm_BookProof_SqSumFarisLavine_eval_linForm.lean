-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_eval_linForm
-- name    : BookProof.SqSumFarisLavine.eval_linForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:15.686991+00:00
-- url     : https://prove2.me/theorems/e9b2cc1d-4c52-4c99-836d-d09df7144284
-- title:
--   (v : Fin D → ℝ) (x : Vd D) : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linForm v) = ((linFun v x : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.eval_linForm` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.eval_linForm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.eval_linForm (v : Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linForm v) = ((linFun v x : ℝ) : ℂ) := by sorry
