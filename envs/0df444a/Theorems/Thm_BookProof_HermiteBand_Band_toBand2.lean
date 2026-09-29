-- Prove2me | Theorems.Thm_BookProof_HermiteBand_Band_toBand2
-- name    : BookProof.HermiteBand.Band.toBand2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:29.171074+00:00
-- url     : https://prove2.me/theorems/e83a308a-3203-4bbb-8c43-a31d1990d189
-- title:
--   The Lean 4 theorem `toBand2` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `toBand2` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.Band.toBand2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.Band.toBand2 {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (h : Band T 1 M C g1) : Band T 2 M C g2 := by sorry
