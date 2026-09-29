-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_gaussInt_harm_self
-- name    : BookProof.HermiteQuadraticEsa.gaussInt_harm_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:35.828944+00:00
-- url     : https://prove2.me/theorems/1f571a09-8582-40cd-b8b4-1a30f338fd04
-- title:
--   The Lean 4 theorem `gaussInt_harm_self` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_harm_self` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.gaussInt_harm_self
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.gaussInt_harm_self (q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly q * (harmPoly * q))
      = (((∑ k : Fin d, ‖pgLp (X k * q)‖ ^ 2) / 4 : ℝ) : ℂ) := by sorry
