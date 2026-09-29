-- Prove2me | Theorems.Thm_BookProof_HermiteBand_degree_add_single
-- name    : BookProof.HermiteBand.degree_add_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T11:59:36.914385+00:00
-- url     : https://prove2.me/theorems/e04edd2b-71c9-4f40-abfa-4addfa2795b7
-- title:
--   The Lean 4 theorem `degree_add_single` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `degree_add_single` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.degree_add_single
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.degree_add_single (α : Fin d →₀ ℕ) (i : Fin d) :
    (α + Finsupp.single i 1).degree = α.degree + 1 := by sorry
