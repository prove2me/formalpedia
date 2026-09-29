-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
-- name    : BookProof.ShiftedHermiteCore.polyGaussCoreT_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:46.489878+00:00
-- url     : https://prove2.me/theorems/38a7e36b-63f3-47c9-997a-363ab2b47843
-- title:
--   The Lean 4 theorem `polyGaussCoreT_dense` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polyGaussCoreT_dense` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.polyGaussCoreT_dense
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

theorem BookProof.ShiftedHermiteCore.polyGaussCoreT_dense (a k : Vd d) :
    Dense ((polyGaussCoreT a k : Submodule ℂ (L2d d)) : Set (L2d d)) := by sorry
