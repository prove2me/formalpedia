-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
-- name    : BookProof.YangMillsHermite.PolySym.real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:49:31.428624+00:00
-- url     : https://prove2.me/theorems/128bce44-785f-49a5-823f-e8df9298d7d2
-- title:
--   {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) : PolySym (((t : ℂ)) • T)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.PolySym.real_smul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.PolySym.real_smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.PolySym.real_smul {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) :
    PolySym (((t : ℂ)) • T) := by sorry
