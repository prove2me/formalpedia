-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_norm_sq_one
-- name    : BookProof.HermiteQuadraticEsa.norm_sq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:28.468206+00:00
-- url     : https://prove2.me/theorems/342b0100-ccfd-428d-8581-170b1627c8b3
-- title:
--   The Lean 4 theorem `norm_sq_one` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sq_one` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_sq_one
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.norm_sq_one (x : Vd 1) : ‖x‖ ^ 2 = (x 0) ^ 2 := by sorry
