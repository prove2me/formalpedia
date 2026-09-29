-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_abs_coord_zero_le_norm_two
-- name    : BookProof.HermiteQuadraticEsa.abs_coord_zero_le_norm_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:40.112612+00:00
-- url     : https://prove2.me/theorems/af552841-338a-48b8-9ebe-100838787cb9
-- title:
--   The Lean 4 theorem `abs_coord_zero_le_norm_two` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `abs_coord_zero_le_norm_two` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_coord_zero_le_norm_two
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.abs_coord_zero_le_norm_two (x : Vd 2) : |x 0| ≤ ‖x‖ := by sorry
