-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym
-- name    : BookProof.YangMillsHermite.mulOp_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:19:15.72504+00:00
-- url     : https://prove2.me/theorems/eee93cf7-b8f8-4736-a194-55d2717177be
-- title:
--   {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.mulOp_polySym` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.mulOp_polySym
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.mulOp_polySym {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f) := by sorry
