-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand2_sum
-- name    : BookProof.HermiteBand.IsBand2.sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:16:50.212823+00:00
-- url     : https://prove2.me/theorems/1d75cb0b-ebdd-4c6d-a4c5-2092f0368f80
-- title:
--   The Lean 4 theorem `sum` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand2.sum
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand2.sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBand2 (F i)) : IsBand2 (∑ i ∈ s, F i) := by sorry
