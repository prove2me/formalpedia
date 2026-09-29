-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_pgLpT_smul
-- name    : BookProof.ShiftedHermiteCore.pgLpT_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:13.366346+00:00
-- url     : https://prove2.me/theorems/ef546caf-975c-4f23-8329-0ef4a747cb6b
-- title:
--   The Lean 4 theorem `pgLpT_smul` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLpT_smul` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.pgLpT_smul
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedHermiteCore










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedHermiteCore.pgLpT_smul (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    pgLpT a k (c • p) = c • pgLpT a k p := by sorry
