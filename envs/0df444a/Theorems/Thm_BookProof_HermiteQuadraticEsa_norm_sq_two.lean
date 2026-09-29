-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_norm_sq_two
-- name    : BookProof.HermiteQuadraticEsa.norm_sq_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:09.227932+00:00
-- url     : https://prove2.me/theorems/bb7c0ad9-fd09-4054-9655-3619dab23c41
-- title:
--   The Lean 4 theorem `norm_sq_two` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sq_two` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_sq_two
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.norm_sq_two (x : Vd 2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by sorry
