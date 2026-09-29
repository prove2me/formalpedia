-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hermiteCore_friedrichs_extension
-- name    : BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:14.932055+00:00
-- url     : https://prove2.me/theorems/67ad1880-ca7a-4fd3-b46c-2e4f4daebd68
-- title:
--   The Lean 4 theorem `hermiteCore_friedrichs_extension` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteCore_friedrichs_extension` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension
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

theorem BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsSemiboundedSelfAdjointExtension c (hamCore W hWc hWb) A := by sorry
