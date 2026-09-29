-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_sum_gradFun_sq_le_of_schur
-- name    : BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:04:58.052043+00:00
-- url     : https://prove2.me/theorems/712449be-62ea-424c-86c8-09fd97651325
-- title:
--   {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) : ∑ k : Fin D, (gradFun v k x)...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    ∑ k : Fin D, (gradFun v k x) ^ 2 ≤ (a * b) ^ 2 * ‖x‖ ^ 2 := by sorry
