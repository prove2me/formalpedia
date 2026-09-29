-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_L2_eq
-- name    : BookProof.QgHermiteFriedrichs.inner_L2_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:12:13.51023+00:00
-- url     : https://prove2.me/theorems/73967586-dd74-478f-80b8-f56e8d1ad43c
-- title:
--   The Lean 4 theorem `inner_L2_eq` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_L2_eq` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.inner_L2_eq
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

theorem BookProof.QgHermiteFriedrichs.inner_L2_eq (f g : L2d d) :
    (inner ℂ f g : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) ((f : Vd d → ℂ) x) * (g : Vd d → ℂ) x := by sorry
