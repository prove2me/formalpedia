-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_smul
-- name    : BookProof.YangMillsHermite.starP_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:20:02.388979+00:00
-- url     : https://prove2.me/theorems/5ae040e9-2e6c-481e-9939-e471bc05b46d
-- title:
--   (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : starP (c • p) = ((starRingEnd ℂ) c) • starP p
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_smul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by sorry
