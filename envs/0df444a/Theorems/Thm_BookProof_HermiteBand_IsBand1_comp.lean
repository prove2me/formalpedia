-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand1_comp
-- name    : BookProof.HermiteBand.IsBand1.comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:14:39.103988+00:00
-- url     : https://prove2.me/theorems/eb0d32d2-60de-4437-84fb-4ae4dec79e21
-- title:
--   The Lean 4 theorem `comp` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comp` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand1.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand1.comp {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBand1 U) (hT : IsBand1 T) : IsBand2 (U ∘ₗ T) := by sorry
