-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_X
-- name    : BookProof.YangMillsHermite.starP_X
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:03:56.285259+00:00
-- url     : https://prove2.me/theorems/b66f7523-a06c-4eb5-8613-90b0d8908100
-- title:
--   (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_X` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_X
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_X (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by sorry
