-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_quadraticGrowth_essentiallySelfAdjoint
-- name    : BookProof.HermiteQuadraticEsa.quadraticGrowth_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:40.941578+00:00
-- url     : https://prove2.me/theorems/905f6d19-31b8-44f5-b4dc-d20d916a0037
-- title:
--   The Lean 4 theorem `quadraticGrowth_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadraticGrowth_essentiallySelfAdjoint` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.quadraticGrowth_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.quadraticGrowth_essentiallySelfAdjoint {U : Vd d → ℝ} (hUc : Continuous U)
    (hUb : ExpBounded U) {A Ccoef B : ℝ} (hA : 0 ≤ A) (hA1 : 4 * A < 1)
    (hB : 0 ≤ B) (hU : ∀ x, |U x - harmW x| ≤ A * ‖x‖ ^ 2 + Ccoef * ‖x‖ + B) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (hamCore U hUc hUb) := by sorry
