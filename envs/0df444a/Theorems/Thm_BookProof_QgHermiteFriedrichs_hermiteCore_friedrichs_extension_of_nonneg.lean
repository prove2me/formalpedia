-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hermiteCore_friedrichs_extension_of_nonneg
-- name    : BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension_of_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:37.755446+00:00
-- url     : https://prove2.me/theorems/413c3f23-674b-4d35-b94b-178276bed2b2
-- title:
--   The Lean 4 theorem `hermiteCore_friedrichs_extension_of_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteCore_friedrichs_extension_of_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension_of_nonneg
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

theorem BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension_of_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) :
    ∃ (Dom : Submodule ℂ (L2d d)) (A : Dom →ₗ[ℂ] L2d d),
      IsPositiveSelfAdjointExtension (hamCore W hWc hWb) A := by sorry
