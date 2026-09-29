-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
-- name    : BookProof.YangMillsHermite.momOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:01:46.741344+00:00
-- url     : https://prove2.me/theorems/18a4ce88-faee-4dc9-a816-5219a0baf213
-- title:
--   (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.momOp_apply` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.momOp_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := by sorry
