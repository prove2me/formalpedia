-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_momTPoly_apply
-- name    : BookProof.ShiftedHermiteCore.momTPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:17.016443+00:00
-- url     : https://prove2.me/theorems/3a04de16-d53b-48dc-8c41-2acc87608898
-- title:
--   The Lean 4 theorem `momTPoly_apply` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momTPoly_apply` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.momTPoly_apply
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

theorem BookProof.ShiftedHermiteCore.momTPoly_apply (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momTPoly k i p = momPoly i p + ((k i : ℝ) : ℂ) • p := by sorry
