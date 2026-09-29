-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_potLp_pgLp
-- name    : BookProof.QgHermiteFriedrichs.inner_potLp_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:49.175599+00:00
-- url     : https://prove2.me/theorems/1bb27cf1-12c7-4f7d-addc-767cb54d76c9
-- title:
--   The Lean 4 theorem `inner_potLp_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_potLp_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.inner_potLp_pgLp
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

theorem BookProof.QgHermiteFriedrichs.inner_potLp_pgLp (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (((W x : ℝ) : ℂ) * pgFun p x) * pgFun q x := by sorry
