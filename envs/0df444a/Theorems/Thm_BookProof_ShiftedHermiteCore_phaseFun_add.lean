-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_phaseFun_add
-- name    : BookProof.ShiftedHermiteCore.phaseFun_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:20.600361+00:00
-- url     : https://prove2.me/theorems/8edb0d5e-690c-4ca4-8692-4946e608acd9
-- title:
--   The Lean 4 theorem `phaseFun_add` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `phaseFun_add` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.phaseFun_add
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

theorem BookProof.ShiftedHermiteCore.phaseFun_add (k x y : Vd d) : phaseFun k (x + y) = phaseFun k x * phaseFun k y := by sorry
