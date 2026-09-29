-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_symm
-- name    : BookProof.YangMillsHermite.CoreRep.coe_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:54:48.475472+00:00
-- url     : https://prove2.me/theorems/1d472928-bfc2-4dd6-aa85-1934b6497dc6
-- title:
--   (Φ : CoreRep d D) (x : D) : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.CoreRep.coe_symm` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.CoreRep.coe_symm
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

theorem BookProof.YangMillsHermite.CoreRep.coe_symm (Φ : CoreRep d D) (x : D) : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := by sorry
