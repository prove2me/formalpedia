-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_sub
-- name    : BookProof.YangMillsHermite.starP_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:07:21.080241+00:00
-- url     : https://prove2.me/theorems/4d615648-823a-4e02-8c0d-a75dde99a9cc
-- title:
--   (p q : MvPolynomial (Fin d) ℂ) : starP (p - q) = starP p - starP q
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_sub` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_sub
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_sub (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := by sorry
