-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_add
-- name    : BookProof.ShiftedHermiteCore.pgFunT_apply_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:49.229554+00:00
-- url     : https://prove2.me/theorems/a57ce4b4-385d-498e-ae18-e71f30cc984b
-- title:
--   The Lean 4 theorem `pgFunT_apply_add` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFunT_apply_add` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.pgFunT_apply_add
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

theorem BookProof.ShiftedHermiteCore.pgFunT_apply_add (a k : Vd d) (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (p + q) x = pgFunT a k p x + pgFunT a k q x := by sorry
