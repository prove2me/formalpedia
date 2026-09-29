-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_hasDerivAt_pgFunT_sec
-- name    : BookProof.ShiftedHermiteCore.hasDerivAt_pgFunT_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:15:29.871366+00:00
-- url     : https://prove2.me/theorems/68cbece6-5897-4ae9-8bfb-0fc850eea569
-- title:
--   The Lean 4 theorem `hasDerivAt_pgFunT_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_pgFunT_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.hasDerivAt_pgFunT_sec
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

theorem BookProof.ShiftedHermiteCore.hasDerivAt_pgFunT_sec (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => pgFunT a k p (sec i x t))
      (pgFunT a k (dPoly i p) x + (Complex.I * ((k i : ℝ) : ℂ)) * pgFunT a k p x) (x i) := by sorry
