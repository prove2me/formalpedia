-- Prove2me | Theorems.Thm_BookProof_HermiteQuadraticEsa_tendsto_starobinskyV_div_sq
-- name    : BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T13:31:28.177299+00:00
-- url     : https://prove2.me/theorems/247501a9-896f-4a0c-8651-a8d6f6facac1
-- title:
--   The Lean 4 theorem `tendsto_starobinskyV_div_sq` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `tendsto_starobinskyV_div_sq` in the `ChapterHermiteQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq (M alpha : ℝ) :
    Filter.Tendsto (fun phi : ℝ => starobinskyV M alpha phi / phi ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (M ^ 2 / (24 * alpha))) := by sorry
