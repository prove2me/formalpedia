-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_sectorQuadW
-- name    : BookProof.HermiteQuadraticEsa.continuous_sectorQuadW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:43.690146+00:00
-- url     : https://prove2.me/theorems/c11255d3-e370-4811-8e41-53d03a305a1b
-- title:
--   The Lean 4 theorem `continuous_sectorQuadW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `continuous_sectorQuadW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.continuous_sectorQuadW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.continuous_sectorQuadW (M alpha mu : ℝ) : Continuous (sectorQuadW M alpha mu) := by sorry
