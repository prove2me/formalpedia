-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_coreEquivT_coe
-- name    : BookProof.ShiftedHermiteCore.coreEquivT_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:10:57.450273+00:00
-- url     : https://prove2.me/theorems/58fac682-9e99-44d0-9e6a-f596561094c1
-- title:
--   The Lean 4 theorem `coreEquivT_coe` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreEquivT_coe` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.coreEquivT_coe
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

theorem BookProof.ShiftedHermiteCore.coreEquivT_coe (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquivT a k p : polyGaussCoreT a k) : L2d d) = pgLpT a k p := by sorry
