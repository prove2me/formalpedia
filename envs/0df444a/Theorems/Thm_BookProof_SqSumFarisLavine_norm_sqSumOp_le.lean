-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumOp_le
-- name    : BookProof.SqSumFarisLavine.norm_sqSumOp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T09:13:23.900023+00:00
-- url     : https://prove2.me/theorems/4c254878-ced3-474a-a90f-105fa3dd414a
-- title:
--   The Lean 4 theorem `norm_sqSumOp_le` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sqSumOp_le` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.norm_sqSumOp_le
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.GaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFock
open BookProof.SqSumFarisLavine

variable {D : ℕ} {R : Type*} [Fintype R]



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

theorem BookProof.SqSumFarisLavine.norm_sqSumOp_le {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (u : polyGaussCore (d := D)) :
    ‖sqSumOp kappa v u‖ ≤ (3 / 2 * km + 8 * B) * ‖harmCore u + (u : L2d D)‖ := by sorry
