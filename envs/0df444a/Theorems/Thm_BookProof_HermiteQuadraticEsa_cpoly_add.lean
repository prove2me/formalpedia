-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_cpoly_add
-- name    : BookProof.HermiteQuadraticEsa.cpoly_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:54.712855+00:00
-- url     : https://prove2.me/theorems/e81100ec-1be6-45b4-bfcc-4ba4ca80eedc
-- title:
--   The Lean 4 theorem `cpoly_add` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_add` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.cpoly_add
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.cpoly_add (p q : MvPolynomial (Fin d) ℂ) : cpoly (p + q) = cpoly p + cpoly q := by sorry
