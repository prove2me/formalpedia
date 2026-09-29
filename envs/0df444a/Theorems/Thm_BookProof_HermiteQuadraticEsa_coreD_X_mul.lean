-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_coreD_X_mul
-- name    : BookProof.HermiteQuadraticEsa.coreD_X_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:50.511855+00:00
-- url     : https://prove2.me/theorems/397de3eb-52ab-4ba2-b11a-b4d2045b30d5
-- title:
--   The Lean 4 theorem `coreD_X_mul` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreD_X_mul` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.coreD_X_mul
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.coreD_X_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (X j * p) = p + X j * coreD j p := by sorry
