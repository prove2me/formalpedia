-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_CoreRep_op_apply
-- name    : BookProof.YangMillsHermite.CoreRep.op_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:55:40.152566+00:00
-- url     : https://prove2.me/theorems/7f8f2fc7-5bb0-4fc7-994c-fbb845e8e3c2
-- title:
--   (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) : Φ.op T x = Φ.equiv (T (Φ.equiv.symm x))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.CoreRep.op_apply` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.CoreRep.op_apply
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsHermite.CoreRep







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}

theorem BookProof.YangMillsHermite.CoreRep.op_apply (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    Φ.op T x = Φ.equiv (T (Φ.equiv.symm x)) := by sorry
