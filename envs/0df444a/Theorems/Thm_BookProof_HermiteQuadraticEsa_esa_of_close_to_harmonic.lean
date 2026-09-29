-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_esa_of_close_to_harmonic
-- name    : BookProof.HermiteQuadraticEsa.esa_of_close_to_harmonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:45.594759+00:00
-- url     : https://prove2.me/theorems/2d8916e1-40ed-46bf-bc5d-b0c1b10add17
-- title:
--   The Lean 4 theorem `esa_of_close_to_harmonic` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `esa_of_close_to_harmonic` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.esa_of_close_to_harmonic
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.esa_of_close_to_harmonic {U : Vd d → ℝ} (hUc : Continuous U) (hUb : ExpBounded U)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hU : ∀ x, |U x - harmW x| ≤ a * harmW x + b) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (hamCore U hUc hUb) := by sorry
