-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
-- name    : BookProof.YangMillsHermite.CoreRep.coe_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:13:43.027932+00:00
-- url     : https://prove2.me/theorems/2e08c519-364f-4d10-b03c-b18aa26f210b
-- title:
--   (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) : ((Φ.op T x : D) : L2d d) = pgLp (T (Φ.equiv.symm x))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.CoreRep.coe_op` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.CoreRep.coe_op
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

theorem BookProof.YangMillsHermite.CoreRep.coe_op (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    ((Φ.op T x : D) : L2d d) = pgLp (T (Φ.equiv.symm x)) := by sorry
