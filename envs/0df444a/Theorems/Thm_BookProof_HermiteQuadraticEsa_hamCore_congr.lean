-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_hamCore_congr
-- name    : BookProof.HermiteQuadraticEsa.hamCore_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:30:54.906767+00:00
-- url     : https://prove2.me/theorems/5ca236cb-11d3-4171-841f-3d4f3ee05969
-- title:
--   The Lean 4 theorem `hamCore_congr` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_congr` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.hamCore_congr
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.hamCore_congr {U U' : Vd d → ℝ} (h : U = U') (hUc : Continuous U) (hUb : ExpBounded U)
    (hU'c : Continuous U') (hU'b : ExpBounded U') :
    hamCore U hUc hUb = hamCore U' hU'c hU'b := by sorry
