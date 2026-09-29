-- Prove2me | Theorems.Thm_BookProof_HermiteBand_degree_sub_single
-- name    : BookProof.HermiteBand.degree_sub_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:00:04.543126+00:00
-- url     : https://prove2.me/theorems/01ff5b21-612c-42fc-96b4-5e19500e219b
-- title:
--   The Lean 4 theorem `degree_sub_single` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `degree_sub_single` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.degree_sub_single
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.degree_sub_single {α : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ α i) :
    (α - Finsupp.single i 1).degree + 1 = α.degree := by sorry
