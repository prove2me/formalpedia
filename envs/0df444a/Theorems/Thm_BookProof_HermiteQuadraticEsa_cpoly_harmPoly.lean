-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_cpoly_harmPoly
-- name    : BookProof.HermiteQuadraticEsa.cpoly_harmPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:59.13906+00:00
-- url     : https://prove2.me/theorems/a450a3e9-f5b0-4938-89ca-0ca1ca3d0afe
-- title:
--   The Lean 4 theorem `cpoly_harmPoly` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_harmPoly` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.cpoly_harmPoly
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.cpoly_harmPoly : cpoly (harmPoly (d := d)) = harmPoly := by sorry
