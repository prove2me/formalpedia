-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_mulXTPoly_apply
-- name    : BookProof.ShiftedHermiteCore.mulXTPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:37.371931+00:00
-- url     : https://prove2.me/theorems/964955f5-1146-47b9-8485-94ba12bea3d2
-- title:
--   The Lean 4 theorem `mulXTPoly_apply` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulXTPoly_apply` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.mulXTPoly_apply
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

theorem BookProof.ShiftedHermiteCore.mulXTPoly_apply (a : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXTPoly a i p = X i * p + ((a i : ℝ) : ℂ) • p := by sorry
