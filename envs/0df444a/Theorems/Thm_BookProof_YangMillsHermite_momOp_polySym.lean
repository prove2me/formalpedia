-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym
-- name    : BookProof.YangMillsHermite.momOp_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:26:45.000985+00:00
-- url     : https://prove2.me/theorems/f1413666-1bc6-4c9c-83ed-78cf09176736
-- title:
--   (j : Fin d) : PolySym (momOp (d
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.momOp_polySym` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.momOp_polySym
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.momOp_polySym (j : Fin d) : PolySym (momOp (d := d) j) := by sorry
