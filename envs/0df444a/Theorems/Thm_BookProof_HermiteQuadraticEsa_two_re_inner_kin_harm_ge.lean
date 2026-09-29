-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_two_re_inner_kin_harm_ge
-- name    : BookProof.HermiteQuadraticEsa.two_re_inner_kin_harm_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:16.289087+00:00
-- url     : https://prove2.me/theorems/9e604725-82e4-4285-a2d9-0131aaaaa58b
-- title:
--   The Lean 4 theorem `two_re_inner_kin_harm_ge` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `two_re_inner_kin_harm_ge` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.two_re_inner_kin_harm_ge
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.two_re_inner_kin_harm_ge (p : MvPolynomial (Fin d) ℂ) :
    -((d : ℝ) / 2) * ‖pgLp p‖ ^ 2
      ≤ 2 * (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ).re := by sorry
