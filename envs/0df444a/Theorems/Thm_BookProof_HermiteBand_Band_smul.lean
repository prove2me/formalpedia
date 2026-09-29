-- Prove2me | Theorems.Thm_BookProof_HermiteBand_Band_smul
-- name    : BookProof.HermiteBand.Band.smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:15.339691+00:00
-- url     : https://prove2.me/theorems/cd7c8941-6f7b-4544-8163-ea0682492807
-- title:
--   The Lean 4 theorem `smul` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smul` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.Band.smul
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.Band.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M : ℕ}
    {C : ℝ} {g : ℕ → ℝ} (c : ℂ) (h : Band T r M C g) :
    Band (c • T) r M (‖c‖ * C) g := by sorry
