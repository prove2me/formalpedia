-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_C
-- name    : BookProof.YangMillsHermite.starP_C
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:03:19.232314+00:00
-- url     : https://prove2.me/theorems/91591f4a-016f-4557-9bea-d7b1fcc0b37e
-- title:
--   (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_C` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_C
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_C (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by sorry
