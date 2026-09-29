-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_norm_sq_harmPoly_mul_le
-- name    : BookProof.HermiteQuadraticEsa.norm_sq_harmPoly_mul_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:31.297971+00:00
-- url     : https://prove2.me/theorems/eca2c453-6097-4f28-b8f2-c73956e3be75
-- title:
--   The Lean 4 theorem `norm_sq_harmPoly_mul_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sq_harmPoly_mul_le` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_sq_harmPoly_mul_le
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.norm_sq_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖ ^ 2
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ ^ 2 + ((d : ℝ) / 2) * ‖pgLp p‖ ^ 2 := by sorry
