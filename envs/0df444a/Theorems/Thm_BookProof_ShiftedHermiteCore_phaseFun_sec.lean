-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_phaseFun_sec
-- name    : BookProof.ShiftedHermiteCore.phaseFun_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:34.294839+00:00
-- url     : https://prove2.me/theorems/d416b0b7-68d5-413a-abb6-0dbf5f87dfa1
-- title:
--   The Lean 4 theorem `phaseFun_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `phaseFun_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.phaseFun_sec
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

theorem BookProof.ShiftedHermiteCore.phaseFun_sec (k x : Vd d) (i : Fin d) (t : ℝ) :
    phaseFun k (sec i x t)
      = phaseFun k x * Complex.exp (Complex.I * (((k i * (t - x i) : ℝ)) : ℂ)) := by sorry
