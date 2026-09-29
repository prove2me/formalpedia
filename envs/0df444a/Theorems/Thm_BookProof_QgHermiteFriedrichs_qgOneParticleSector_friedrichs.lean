-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_qgOneParticleSector_friedrichs
-- name    : BookProof.QgHermiteFriedrichs.qgOneParticleSector_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:04:26.187973+00:00
-- url     : https://prove2.me/theorems/e68e999d-88d8-4a46-9d87-28caa9ccb0ee
-- title:
--   The Lean 4 theorem `qgOneParticleSector_friedrichs` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOneParticleSector_friedrichs` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.qgOneParticleSector_friedrichs
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
import Theorems.Thm_BookProof_QgHermiteCore_continuous_scalaronSectorPotential
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_scalaronSectorPotential
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.qgOneParticleSector_friedrichs (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    ∃ (Dom : Submodule ℂ (L2d 2)) (A : Dom →ₗ[ℂ] L2d 2),
      IsSemiboundedSelfAdjointExtension c
        (hamCore (scalaronSectorPotential M alpha V3)
          (continuous_scalaronSectorPotential M alpha V3)
          (expBounded_scalaronSectorPotential M alpha hM V3)) A := by sorry
