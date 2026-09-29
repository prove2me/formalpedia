-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_eval_gradPoly
-- name    : BookProof.SqSumFarisLavine.eval_gradPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:54:48.799287+00:00
-- url     : https://prove2.me/theorems/d040dce2-45f7-42a0-9a9e-64ed2c237c9a
-- title:
--   (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gradPoly v k) = ((gradFun v k x : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.eval_gradPoly` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.eval_gradPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.eval_gradPoly (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gradPoly v k) = ((gradFun v k x : ℝ) : ℂ) := by sorry
