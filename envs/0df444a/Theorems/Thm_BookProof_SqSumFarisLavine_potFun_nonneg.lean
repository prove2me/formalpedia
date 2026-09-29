-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_potFun_nonneg
-- name    : BookProof.SqSumFarisLavine.potFun_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:28.378639+00:00
-- url     : https://prove2.me/theorems/c65eee45-fe60-4d62-a855-6d9e09204756
-- title:
--   (v : R → Fin D → ℝ) (x : Vd D) : 0 ≤ potFun v x
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.potFun_nonneg` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.potFun_nonneg
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.potFun_nonneg (v : R → Fin D → ℝ) (x : Vd D) : 0 ≤ potFun v x := by sorry
