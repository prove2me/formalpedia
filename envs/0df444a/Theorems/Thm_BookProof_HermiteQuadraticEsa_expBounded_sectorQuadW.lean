-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_sectorQuadW
-- name    : BookProof.HermiteQuadraticEsa.expBounded_sectorQuadW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:27.358649+00:00
-- url     : https://prove2.me/theorems/95a981d1-f577-4efe-a689-5d1374aba477
-- title:
--   The Lean 4 theorem `expBounded_sectorQuadW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_sectorQuadW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_sectorQuadW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.expBounded_sectorQuadW (M alpha mu : ℝ) : ExpBounded (sectorQuadW M alpha mu) := by sorry
