-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_mul_self
-- name    : BookProof.QgHermiteFriedrichs.conj_mul_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:02:19.468393+00:00
-- url     : https://prove2.me/theorems/93b94d5a-ab8a-4d59-a914-9a21a1b0423f
-- title:
--   The Lean 4 theorem `conj_mul_self` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `conj_mul_self` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.conj_mul_self
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

theorem BookProof.QgHermiteFriedrichs.conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by sorry
