-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul
-- name    : BookProof.YangMillsHermite.RealCoeff.smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:50:22.087566+00:00
-- url     : https://prove2.me/theorems/154f790b-185e-4122-ba0c-1cca7fa410e4
-- title:
--   {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) : RealCoeff ((t : ℂ) • p)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.RealCoeff.smul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.RealCoeff.smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.RealCoeff.smul {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) :
    RealCoeff ((t : ℂ) • p) := by sorry
