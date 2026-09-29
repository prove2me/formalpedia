-- Prove2me | Theorems.Thm_BookProof_HermiteBand_g1_nonneg
-- name    : BookProof.HermiteBand.g1_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:00:27.501403+00:00
-- url     : https://prove2.me/theorems/1be892d7-37c6-4643-839a-d292a4e92512
-- title:
--   The Lean 4 theorem `g1_nonneg` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `g1_nonneg` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.g1_nonneg
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.g1_nonneg (n : ℕ) : 0 ≤ g1 n := by sorry
