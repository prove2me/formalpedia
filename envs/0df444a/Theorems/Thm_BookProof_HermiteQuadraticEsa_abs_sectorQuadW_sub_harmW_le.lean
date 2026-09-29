-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_abs_sectorQuadW_sub_harmW_le
-- name    : BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:50.865008+00:00
-- url     : https://prove2.me/theorems/e944a891-4606-4a88-a89d-5e2757fb9c8c
-- title:
--   The Lean 4 theorem `abs_sectorQuadW_sub_harmW_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `abs_sectorQuadW_sub_harmW_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le (M alpha mu : ℝ) (x : Vd 2) :
    |sectorQuadW M alpha mu x - harmW x|
      ≤ max |alpha - 1 / 4| |mu - 1 / 4| * ‖x‖ ^ 2 + (M ^ 2 / 2) * ‖x‖ + 0 := by sorry
