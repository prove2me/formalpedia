-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_mul
-- name    : BookProof.YangMillsHermite.starP_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:05:23.840314+00:00
-- url     : https://prove2.me/theorems/cfb41db6-1053-4fac-b832-b7a5bfe69732
-- title:
--   (p q : MvPolynomial (Fin d) ℂ) : starP (p * q) = starP p * starP q
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_mul` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_mul
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_mul (p q : MvPolynomial (Fin d) ℂ) :
    starP (p * q) = starP p * starP q := by sorry
