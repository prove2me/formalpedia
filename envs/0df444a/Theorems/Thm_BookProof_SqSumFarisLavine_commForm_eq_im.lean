-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_commForm_eq_im
-- name    : BookProof.SqSumFarisLavine.commForm_eq_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T18:31:01.063989+00:00
-- url     : https://prove2.me/theorems/5ee479e2-2454-4f8a-a226-74df327a07b6
-- title:
--   The Lean 4 theorem `commForm_eq_im` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `commForm_eq_im` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.commForm_eq_im
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.GaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFock
open BookProof.SqSumFarisLavine

variable {D : ℕ} {R : Type*} [Fintype R]



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

theorem BookProof.SqSumFarisLavine.commForm_eq_im (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commForm (sqSumOp kappa v) harmCore ⟨pgLp p, pgLp_mem_core p⟩
      = -(gaussInt (cpoly p * commPoly kappa v p)).im := by sorry
