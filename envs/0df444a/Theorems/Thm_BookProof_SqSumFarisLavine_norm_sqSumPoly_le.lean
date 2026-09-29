-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumPoly_le
-- name    : BookProof.SqSumFarisLavine.norm_sqSumPoly_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:26.505763+00:00
-- url     : https://prove2.me/theorems/321b4f7e-ece7-4287-a38b-ba2f9df974cf
-- title:
--   {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ} (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B) (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p :...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.norm_sqSumPoly_le` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.norm_sqSumPoly_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.norm_sqSumPoly_le {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (sqSumPoly kappa v p)‖ ≤ (3 / 2 * km + 8 * B) * shiftNorm p := by sorry
