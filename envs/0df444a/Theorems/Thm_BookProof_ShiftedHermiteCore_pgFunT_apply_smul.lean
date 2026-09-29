-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_smul
-- name    : BookProof.ShiftedHermiteCore.pgFunT_apply_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:00.763662+00:00
-- url     : https://prove2.me/theorems/f539a29c-eb70-4865-a41e-7eb8c2a0fe57
-- title:
--   The Lean 4 theorem `pgFunT_apply_smul` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFunT_apply_smul` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.pgFunT_apply_smul
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

theorem BookProof.ShiftedHermiteCore.pgFunT_apply_smul (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (c • p) x = c * pgFunT a k p x := by sorry
