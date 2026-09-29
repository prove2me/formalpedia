-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_neg
-- name    : BookProof.YangMillsHermite.starP_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:06:06.062544+00:00
-- url     : https://prove2.me/theorems/3924f5b5-a532-4d73-8e77-9909731db572
-- title:
--   (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_neg` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_neg
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_neg (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := by sorry
