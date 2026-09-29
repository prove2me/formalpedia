-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_coreD_harmPoly_mul
-- name    : BookProof.HermiteQuadraticEsa.coreD_harmPoly_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:58.765241+00:00
-- url     : https://prove2.me/theorems/562e68f3-841e-447a-8df7-48fcad557a44
-- title:
--   The Lean 4 theorem `coreD_harmPoly_mul` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreD_harmPoly_mul` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.coreD_harmPoly_mul
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.coreD_harmPoly_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (harmPoly * p) = C (1 / 2 : ℂ) * (X j * p) + harmPoly * coreD j p := by sorry
