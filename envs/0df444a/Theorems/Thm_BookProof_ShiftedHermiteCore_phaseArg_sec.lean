-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_phaseArg_sec
-- name    : BookProof.ShiftedHermiteCore.phaseArg_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:13.402985+00:00
-- url     : https://prove2.me/theorems/acf0823f-3fb7-4618-b8da-0ba51115789d
-- title:
--   The Lean 4 theorem `phaseArg_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `phaseArg_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.phaseArg_sec
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

theorem BookProof.ShiftedHermiteCore.phaseArg_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseArg k (sec i x t) = phaseArg k x + k i * (t - x i) := by sorry
