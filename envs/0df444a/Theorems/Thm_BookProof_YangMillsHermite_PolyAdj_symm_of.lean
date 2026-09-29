-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_PolyAdj_symm_of
-- name    : BookProof.YangMillsHermite.PolyAdj.symm_of
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:42:51.907048+00:00
-- url     : https://prove2.me/theorems/a0ac68c3-51f6-4725-b552-d19e649a803d
-- title:
--   {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.PolyAdj.symm_of` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.PolyAdj.symm_of
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.PolyAdj.symm_of {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T) := by sorry
