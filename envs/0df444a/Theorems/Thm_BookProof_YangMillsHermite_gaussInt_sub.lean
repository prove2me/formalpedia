-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_gaussInt_sub
-- name    : BookProof.YangMillsHermite.gaussInt_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:59:36.713628+00:00
-- url     : https://prove2.me/theorems/b9e1ba6f-765c-462f-b5b3-373a30eb7679
-- title:
--   (r s : MvPolynomial (Fin d) ℂ) : gaussInt (r - s) = gaussInt r - gaussInt s
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.gaussInt_sub` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.gaussInt_sub
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by sorry
