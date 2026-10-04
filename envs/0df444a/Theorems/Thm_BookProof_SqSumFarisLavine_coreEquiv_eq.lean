-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_coreEquiv_eq
-- name    : BookProof.SqSumFarisLavine.coreEquiv_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T17:02:17.627168+00:00
-- url     : https://prove2.me/theorems/e06e118b-ac17-44b0-9a9a-425c9a4be318
-- title:
--   The Lean 4 theorem `coreEquiv_eq` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreEquiv_eq` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.coreEquiv_eq
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.SqSumFarisLavine

variable {D : ℕ} {R : Type*} [Fintype R]



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

theorem BookProof.SqSumFarisLavine.coreEquiv_eq (p : MvPolynomial (Fin D) ℂ) :
    BookProof.NavierStokesFlow.DifferentialL2.coreEquiv p
      = (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := D)) := by sorry
