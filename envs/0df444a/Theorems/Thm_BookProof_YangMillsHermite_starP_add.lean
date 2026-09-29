-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_add
-- name    : BookProof.YangMillsHermite.starP_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:04:36.032666+00:00
-- url     : https://prove2.me/theorems/10e0d1fe-ab03-4554-8495-bd1134a7af2f
-- title:
--   (p q : MvPolynomial (Fin d) ℂ) : starP (p + q) = starP p + starP q
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_add` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_add
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_add (p q : MvPolynomial (Fin d) ℂ) :
    starP (p + q) = starP p + starP q := by sorry
