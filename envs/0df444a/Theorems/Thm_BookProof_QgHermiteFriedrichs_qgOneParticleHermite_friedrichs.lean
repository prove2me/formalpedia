-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_qgOneParticleHermite_friedrichs
-- name    : BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:04:45.285776+00:00
-- url     : https://prove2.me/theorems/cc497bcb-46fc-41e8-872c-cea5c9fa2870
-- title:
--   The Lean 4 theorem `qgOneParticleHermite_friedrichs` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOneParticleHermite_friedrichs` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_QgHermiteFriedrichs_continuous_scalaronW
import Theorems.Thm_BookProof_QgHermiteFriedrichs_expBounded_scalaronW
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    ∃ (Dom : Submodule ℂ (L2d 1)) (A : Dom →ₗ[ℂ] L2d 1),
      IsPositiveSelfAdjointExtension
        (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha)
          (expBounded_scalaronW M alpha hM)) A := by sorry
