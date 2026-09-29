-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_of_growth_bound
-- name    : BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:29.99781+00:00
-- url     : https://prove2.me/theorems/0506ec43-e10f-490d-a378-ca98ac5726fb
-- title:
--   The Lean 4 theorem `expBounded_of_growth_bound` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_of_growth_bound` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound {U : Vd d → ℝ} {A Ccoef B : ℝ} (hA : 0 ≤ A)
    (hC : 0 ≤ Ccoef) (hB : 0 ≤ B)
    (hU : ∀ x, |U x - harmW x| ≤ A * ‖x‖ ^ 2 + Ccoef * ‖x‖ + B) :
    ExpBounded U := by sorry
