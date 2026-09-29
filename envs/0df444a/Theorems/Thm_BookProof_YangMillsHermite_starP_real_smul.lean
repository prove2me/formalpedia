-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_real_smul
-- name    : BookProof.YangMillsHermite.starP_real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:22:30.942382+00:00
-- url     : https://prove2.me/theorems/3391091d-0571-430e-8b6f-5d8d3cad6e1c
-- title:
--   (t : ℝ) (p : MvPolynomial (Fin d) ℂ) : starP ((t : ℂ) • p) = (t : ℂ) • starP p
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_real_smul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_real_smul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_real_smul (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by sorry
