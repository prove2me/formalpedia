-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_inner_pgLpT_left
-- name    : BookProof.ShiftedHermiteCore.inner_pgLpT_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:26.520009+00:00
-- url     : https://prove2.me/theorems/f5df7be8-b8f8-4cdb-9fa9-f620b56d3bf1
-- title:
--   The Lean 4 theorem `inner_pgLpT_left` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_pgLpT_left` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.inner_pgLpT_left
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

theorem BookProof.ShiftedHermiteCore.inner_pgLpT_left (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) (u : L2d d) :
    (inner ℂ (pgLpT a k p) u : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFunT a k p x) * (u : Vd d → ℂ) x := by sorry
