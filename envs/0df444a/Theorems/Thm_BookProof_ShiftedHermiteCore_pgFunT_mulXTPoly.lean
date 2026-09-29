-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_mulXTPoly
-- name    : BookProof.ShiftedHermiteCore.pgFunT_mulXTPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:05.080745+00:00
-- url     : https://prove2.me/theorems/5bd01b37-3ced-4906-87ff-5b140b388059
-- title:
--   The Lean 4 theorem `pgFunT_mulXTPoly` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFunT_mulXTPoly` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.pgFunT_mulXTPoly
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

theorem BookProof.ShiftedHermiteCore.pgFunT_mulXTPoly (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (mulXTPoly a i p) x = ((x i : ℝ) : ℂ) * pgFunT a k p x := by sorry
