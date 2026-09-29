-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_span_hermiteTLp
-- name    : BookProof.ShiftedHermiteCore.span_hermiteTLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:27.72566+00:00
-- url     : https://prove2.me/theorems/2b9e2882-46ec-4227-87f5-a0f2cc9b81fd
-- title:
--   The Lean 4 theorem `span_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `span_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.span_hermiteTLp
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

theorem BookProof.ShiftedHermiteCore.span_hermiteTLp (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTLp (d := d) a k)) = polyGaussCoreT a k := by sorry
