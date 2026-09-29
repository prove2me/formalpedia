-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_potLp_symm
-- name    : BookProof.QgHermiteFriedrichs.inner_potLp_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:27:12.05579+00:00
-- url     : https://prove2.me/theorems/dc092a22-d724-4b52-ab3d-d934608f4180
-- title:
--   The Lean 4 theorem `inner_potLp_symm` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_potLp_symm` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.inner_potLp_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.inner_potLp_symm (hWc : Continuous W) (hWb : ExpBounded W)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (potLp W hWc hWb p) (pgLp q) : ℂ) = inner ℂ (pgLp p) (potLp W hWc hWb q) := by sorry
