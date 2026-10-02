-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_commForm_sqSumOp_le
-- name    : BookProof.SqSumFarisLavine.commForm_sqSumOp_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T09:12:43.517698+00:00
-- url     : https://prove2.me/theorems/bdf9206a-0136-472b-9788-97f7d952a036
-- title:
--   The Lean 4 theorem `commForm_sqSumOp_le` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `commForm_sqSumOp_le` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.commForm_sqSumOp_le
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
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

theorem BookProof.SqSumFarisLavine.commForm_sqSumOp_le {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km M : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hM0 : 0 ≤ M)
    (hM : ∀ x : Vd D, ∑ k : Fin D, (gradFun v k x) ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2)
    (u : polyGaussCore (d := D)) :
    |commForm (sqSumOp kappa v) harmCore u| ≤ (km / 2 + 2 * M) * quadForm harmCore u := by sorry
