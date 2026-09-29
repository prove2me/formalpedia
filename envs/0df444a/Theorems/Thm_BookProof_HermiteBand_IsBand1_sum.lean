-- Prove2me | Theorems.Thm_BookProof_HermiteBand_IsBand1_sum
-- name    : BookProof.HermiteBand.IsBand1.sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:06.218186+00:00
-- url     : https://prove2.me/theorems/359b21ba-4da4-44f2-993f-0a4317ebe904
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
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.IsBand1.sum
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.IsBand1.sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBand1 (F i)) : IsBand1 (∑ i ∈ s, F i) := by sorry
