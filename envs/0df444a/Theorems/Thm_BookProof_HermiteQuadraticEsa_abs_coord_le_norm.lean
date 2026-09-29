-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_abs_coord_le_norm
-- name    : BookProof.HermiteQuadraticEsa.abs_coord_le_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:47.552558+00:00
-- url     : https://prove2.me/theorems/9502873f-1b10-4d3d-9e52-b0f04760e3b2
-- title:
--   The Lean 4 theorem `abs_coord_le_norm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `abs_coord_le_norm` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_coord_le_norm
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.abs_coord_le_norm (x : Vd 1) : |x 0| ≤ ‖x‖ := by sorry
