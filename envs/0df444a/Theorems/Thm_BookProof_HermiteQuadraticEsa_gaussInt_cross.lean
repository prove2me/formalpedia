-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_gaussInt_cross
-- name    : BookProof.HermiteQuadraticEsa.gaussInt_cross
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:37.222269+00:00
-- url     : https://prove2.me/theorems/b1b007b1-82e0-4c8e-9102-fbb4df8bc323
-- title:
--   The Lean 4 theorem `gaussInt_cross` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_cross` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.gaussInt_cross
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.gaussInt_cross (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * (X j * p)) + gaussInt (cpoly p * (X j * coreD j p))
      = -gaussInt (cpoly p * p) := by sorry
