-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_norm_potPoly_mul_le
-- name    : BookProof.SqSumFarisLavine.norm_potPoly_mul_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:05:08.539979+00:00
-- url     : https://prove2.me/theorems/b92568e8-0f24-4bf9-acd4-ce13239cd531
-- title:
--   {v : R → Fin D → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (potPoly v * p)‖ ≤ 4 * B * ‖pgLp (harmPoly *...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.norm_potPoly_mul_le` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.norm_potPoly_mul_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.norm_potPoly_mul_le {v : R → Fin D → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (potPoly v * p)‖ ≤ 4 * B * ‖pgLp (harmPoly * p)‖ := by sorry
