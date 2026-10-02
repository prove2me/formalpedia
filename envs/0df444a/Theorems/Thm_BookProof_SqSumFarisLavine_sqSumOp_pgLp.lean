-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_sqSumOp_pgLp
-- name    : BookProof.SqSumFarisLavine.sqSumOp_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T18:29:56.582873+00:00
-- url     : https://prove2.me/theorems/4ae47273-f248-417f-8ac5-7546e5975bde
-- title:
--   The Lean 4 theorem `sqSumOp_pgLp` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sqSumOp_pgLp` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.sqSumOp_pgLp
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
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

theorem BookProof.SqSumFarisLavine.sqSumOp_pgLp (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    sqSumOp kappa v ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (sqSumPoly kappa v p) := by sorry
