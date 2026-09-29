-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_schur_bound
-- name    : BookProof.SqSumFarisLavine.schur_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:43.874146+00:00
-- url     : https://prove2.me/theorems/6db4b250-48f8-4e96-93e3-cd533186c575
-- title:
--   {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℝ) {a b : ℝ} (ha0 : 0 ≤ a) (ha : ∀ i, ∑ j : J, |A i j| ≤ a) (hb : ∀ j, ∑ i : I, |A i j| ≤ b) (y : J → ℝ) : ∑ i : I,...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.schur_bound` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.schur_bound
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.schur_bound {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℝ) {a b : ℝ}
    (ha0 : 0 ≤ a)
    (ha : ∀ i, ∑ j : J, |A i j| ≤ a) (hb : ∀ j, ∑ i : I, |A i j| ≤ b) (y : J → ℝ) :
    ∑ i : I, (∑ j : J, A i j * y j) ^ 2 ≤ a * b * ∑ j : J, (y j) ^ 2 := by sorry
