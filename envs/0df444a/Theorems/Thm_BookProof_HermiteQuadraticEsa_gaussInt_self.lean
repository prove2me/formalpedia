-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_gaussInt_self
-- name    : BookProof.HermiteQuadraticEsa.gaussInt_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:08.900735+00:00
-- url     : https://prove2.me/theorems/489abe22-ab29-48dc-bf36-7633c3f8b43f
-- title:
--   The Lean 4 theorem `gaussInt_self` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_self` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.gaussInt_self
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.gaussInt_self (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly r * r) = ((‖pgLp r‖ ^ 2 : ℝ) : ℂ) := by sorry
