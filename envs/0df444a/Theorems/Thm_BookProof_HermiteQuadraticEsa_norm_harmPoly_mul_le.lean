-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_norm_harmPoly_mul_le
-- name    : BookProof.HermiteQuadraticEsa.norm_harmPoly_mul_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:36.406482+00:00
-- url     : https://prove2.me/theorems/1fde039e-9bbd-44da-9865-c721d6ff6cc3
-- title:
--   The Lean 4 theorem `norm_harmPoly_mul_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_harmPoly_mul_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_harmPoly_mul_le
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.norm_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ + Real.sqrt ((d : ℝ) / 2) * ‖pgLp p‖ := by sorry
