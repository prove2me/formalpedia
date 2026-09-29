-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand1_smul
-- name    : BookProof.HermiteBand.IsBand1.smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:16:58.401971+00:00
-- url     : https://prove2.me/theorems/e10f00b6-5786-4cdf-a8c5-dc74e279ccef
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
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand1.smul
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand1.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ)
    (hT : IsBand1 T) : IsBand1 (c • T) := by sorry
