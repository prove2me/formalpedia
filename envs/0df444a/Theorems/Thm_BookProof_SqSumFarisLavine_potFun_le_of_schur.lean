-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_potFun_le_of_schur
-- name    : BookProof.SqSumFarisLavine.potFun_le_of_schur
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:54:42.23599+00:00
-- url     : https://prove2.me/theorems/b3c5987e-a56c-4073-8da1-79c3b93e7e4f
-- title:
--   {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a) (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) : potFun v x ≤ (a * b / 2) * ‖x‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.potFun_le_of_schur` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.potFun_le_of_schur
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.potFun_le_of_schur {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    potFun v x ≤ (a * b / 2) * ‖x‖ ^ 2 := by sorry
