-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_pgFun
-- name    : BookProof.QgHermiteFriedrichs.conj_pgFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:21:21.545976+00:00
-- url     : https://prove2.me/theorems/f3391ad8-ab17-4f2f-bc32-328cb6283ea0
-- title:
--   The Lean 4 theorem `conj_pgFun` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `conj_pgFun` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.conj_pgFun
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.conj_pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun p x) = pgFun (cpoly p) x := by sorry
