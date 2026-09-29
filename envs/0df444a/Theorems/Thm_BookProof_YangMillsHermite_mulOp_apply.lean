-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
-- name    : BookProof.YangMillsHermite.mulOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:02:30.135738+00:00
-- url     : https://prove2.me/theorems/e2b31265-ea32-48aa-bb70-23c53c01c278
-- title:
--   (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.mulOp_apply` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.mulOp_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := by sorry
