-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_gaussInt_anticommutator
-- name    : BookProof.HermiteQuadraticEsa.gaussInt_anticommutator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:05.749555+00:00
-- url     : https://prove2.me/theorems/cd8a567c-150a-4397-956f-7be7377a3b73
-- title:
--   The Lean 4 theorem `gaussInt_anticommutator` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gaussInt_anticommutator` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.gaussInt_anticommutator
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.gaussInt_anticommutator (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * (harmPoly * p))
        + gaussInt (cpoly (harmPoly * p) * kinPoly p)
      = 2 * (∑ j : Fin d, gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
        - ((d : ℂ) / 2) * gaussInt (cpoly p * p) := by sorry
