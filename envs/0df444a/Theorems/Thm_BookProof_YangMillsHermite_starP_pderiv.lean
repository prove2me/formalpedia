-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_pderiv
-- name    : BookProof.YangMillsHermite.starP_pderiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:06:43.255118+00:00
-- url     : https://prove2.me/theorems/b73d0ff5-b412-49ea-bb99-c0de8da9beb5
-- title:
--   (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : starP (pderiv j p) = pderiv j (starP p)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_pderiv` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_pderiv
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := by sorry
