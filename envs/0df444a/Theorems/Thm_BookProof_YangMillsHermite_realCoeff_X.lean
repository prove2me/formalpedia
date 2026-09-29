-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X
-- name    : BookProof.YangMillsHermite.realCoeff_X
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:15:44.41481+00:00
-- url     : https://prove2.me/theorems/5b183eee-4189-435e-9401-7d6491b5c2cc
-- title:
--   (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.realCoeff_X` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.realCoeff_X
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.realCoeff_X (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := by sorry
