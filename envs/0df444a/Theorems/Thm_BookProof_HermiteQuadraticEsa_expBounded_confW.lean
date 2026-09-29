-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_confW
-- name    : BookProof.HermiteQuadraticEsa.expBounded_confW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:32:18.528559+00:00
-- url     : https://prove2.me/theorems/8e149898-3ed8-413e-aa90-8d1fbddb61d4
-- title:
--   The Lean 4 theorem `expBounded_confW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `expBounded_confW` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_confW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.expBounded_confW (M alpha : ℝ) : ExpBounded (confW M alpha) := by sorry
