-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul
-- name    : BookProof.YangMillsHermite.RealCoeff.mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:45:02.221886+00:00
-- url     : https://prove2.me/theorems/fc74158e-1e2e-4194-bb7e-5d0a034ad57c
-- title:
--   {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) : RealCoeff (p * q)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.RealCoeff.mul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.RealCoeff.mul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.RealCoeff.mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p * q) := by sorry
