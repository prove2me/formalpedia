-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_norm_sq_pgLp
-- name    : BookProof.QgHermiteFriedrichs.norm_sq_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:12:58.474807+00:00
-- url     : https://prove2.me/theorems/1891f2b2-8f66-49c5-9a95-ba8ef24290db
-- title:
--   The Lean 4 theorem `norm_sq_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sq_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.norm_sq_pgLp
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

theorem BookProof.QgHermiteFriedrichs.norm_sq_pgLp (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp p‖ ^ 2 = ∫ x : Vd d, ‖pgFun p x‖ ^ 2 := by sorry
