-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_integrable_potential_normSq
-- name    : BookProof.QgHermiteFriedrichs.integrable_potential_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:41.935871+00:00
-- url     : https://prove2.me/theorems/f32577f2-3b89-423b-8d72-0f78c8d3ce68
-- title:
--   The Lean 4 theorem `integrable_potential_normSq` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integrable_potential_normSq` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.integrable_potential_normSq
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.integrable_potential_normSq (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d => W x * ‖pgFun p x‖ ^ 2) (volume : Measure (Vd d)) := by sorry
