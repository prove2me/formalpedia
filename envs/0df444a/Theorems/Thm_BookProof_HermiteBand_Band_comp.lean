-- Prove2me | Theorems.Thm_BookProof_HermiteBand_Band_comp
-- name    : BookProof.HermiteBand.Band.comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:45.385001+00:00
-- url     : https://prove2.me/theorems/b7db6542-d18c-40f6-bffd-53cde3614139
-- title:
--   The Lean 4 theorem `comp` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comp` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.Band.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.Band.comp {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {M₁ M₂ : ℕ}
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hU : Band U 1 M₂ C₂ g1) (hT : Band T 1 M₁ C₁ g1) :
    Band (U ∘ₗ T) 2 (M₁ * M₂) (2 * M₁ * C₁ * C₂) g2 := by sorry
