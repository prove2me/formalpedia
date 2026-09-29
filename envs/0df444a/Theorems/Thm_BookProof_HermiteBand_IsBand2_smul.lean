-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand2_smul
-- name    : BookProof.HermiteBand.IsBand2.smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:16:38.058401+00:00
-- url     : https://prove2.me/theorems/b8c39201-c6a6-4e9b-9e0b-db77f0175dbb
-- title:
--   The Lean 4 theorem `smul` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smul` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand2.smul
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand2.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ)
    (hT : IsBand2 T) : IsBand2 (c • T) := by sorry
