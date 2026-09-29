-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_derOp_apply
-- name    : BookProof.YangMillsHermite.derOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:57:03.929349+00:00
-- url     : https://prove2.me/theorems/12d1a042-6ce7-44c9-aba3-3930cfa72013
-- title:
--   (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.derOp_apply` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.derOp_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.derOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := by sorry
