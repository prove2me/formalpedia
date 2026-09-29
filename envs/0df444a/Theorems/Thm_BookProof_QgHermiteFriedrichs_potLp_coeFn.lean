-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
-- name    : BookProof.QgHermiteFriedrichs.potLp_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:57.982478+00:00
-- url     : https://prove2.me/theorems/e1308743-0ae7-4911-8e03-8878e4224b85
-- title:
--   The Lean 4 theorem `potLp_coeFn` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `potLp_coeFn` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.potLp_coeFn
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

theorem BookProof.QgHermiteFriedrichs.potLp_coeFn (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x := by sorry
