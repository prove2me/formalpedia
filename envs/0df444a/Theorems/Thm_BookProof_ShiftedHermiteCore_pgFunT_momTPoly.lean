-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_momTPoly
-- name    : BookProof.ShiftedHermiteCore.pgFunT_momTPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:16:09.292174+00:00
-- url     : https://prove2.me/theorems/a9f5ef5b-058d-4728-97fd-72643599c646
-- title:
--   The Lean 4 theorem `pgFunT_momTPoly` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFunT_momTPoly` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.pgFunT_momTPoly
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

theorem BookProof.ShiftedHermiteCore.pgFunT_momTPoly (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (momTPoly k i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i) := by sorry
