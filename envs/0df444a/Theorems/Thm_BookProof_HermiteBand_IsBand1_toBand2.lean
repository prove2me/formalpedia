-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand1_toBand2
-- name    : BookProof.HermiteBand.IsBand1.toBand2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:14:42.7199+00:00
-- url     : https://prove2.me/theorems/54bc09c3-12e9-44f7-bdc0-972641832b3a
-- title:
--   The Lean 4 theorem `toBand2` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `toBand2` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand1.toBand2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand1.toBand2 {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (h : IsBand1 T) : IsBand2 T := by sorry
