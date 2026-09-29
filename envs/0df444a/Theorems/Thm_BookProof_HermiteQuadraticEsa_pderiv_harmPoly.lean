-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_pderiv_harmPoly
-- name    : BookProof.HermiteQuadraticEsa.pderiv_harmPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:19.626847+00:00
-- url     : https://prove2.me/theorems/3c7bbf17-4c48-4a07-a2eb-47aae742922f
-- title:
--   The Lean 4 theorem `pderiv_harmPoly` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_harmPoly` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.pderiv_harmPoly
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.pderiv_harmPoly (j : Fin d) :
    pderiv j (harmPoly (d := d)) = C (1 / 2 : ℂ) * X j := by sorry
