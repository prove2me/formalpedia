-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_gradPoly_self
-- name    : BookProof.SqSumFarisLavine.pderiv_gradPoly_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:54:45.812399+00:00
-- url     : https://prove2.me/theorems/5c8e29d1-6c94-4aaa-ac31-e04a59878008
-- title:
--   (v : R → Fin D → ℝ) (k : Fin D) : pderiv k (gradPoly v k) = C (((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ))
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.pderiv_gradPoly_self` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.pderiv_gradPoly_self
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.pderiv_gradPoly_self (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (gradPoly v k) = C (((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ)) := by sorry
