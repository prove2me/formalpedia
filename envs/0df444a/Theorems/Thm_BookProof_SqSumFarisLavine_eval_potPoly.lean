-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_eval_potPoly
-- name    : BookProof.SqSumFarisLavine.eval_potPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:53:50.319995+00:00
-- url     : https://prove2.me/theorems/b1744bac-3bf1-4273-ad73-2cd0d1cbbd09
-- title:
--   (v : R → Fin D → ℝ) (x : Vd D) : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (potPoly v) = ((potFun v x : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.eval_potPoly` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.eval_potPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.eval_potPoly (v : R → Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (potPoly v) = ((potFun v x : ℝ) : ℂ) := by sorry
