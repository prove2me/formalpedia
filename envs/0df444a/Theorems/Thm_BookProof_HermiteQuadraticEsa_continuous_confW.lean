-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_confW
-- name    : BookProof.HermiteQuadraticEsa.continuous_confW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:26.594835+00:00
-- url     : https://prove2.me/theorems/56c43e66-a2da-47fa-80b0-294c18e1cb79
-- title:
--   The Lean 4 theorem `continuous_confW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `continuous_confW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.continuous_confW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.continuous_confW (M alpha : ℝ) : Continuous (confW M alpha) := by sorry
