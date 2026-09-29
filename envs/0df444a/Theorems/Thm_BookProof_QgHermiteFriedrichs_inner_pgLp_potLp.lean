-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_potLp
-- name    : BookProof.QgHermiteFriedrichs.inner_pgLp_potLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:09.19649+00:00
-- url     : https://prove2.me/theorems/d9ff922a-ffe8-4656-8c91-d4859dfada11
-- title:
--   The Lean 4 theorem `inner_pgLp_potLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_pgLp_potLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.inner_pgLp_potLp
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.inner_pgLp_potLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (potLp W hWc hWb q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (((W x : ℝ) : ℂ) * pgFun q x) := by sorry
