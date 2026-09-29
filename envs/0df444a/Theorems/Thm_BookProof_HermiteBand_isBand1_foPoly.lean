-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand1_foPoly
-- name    : BookProof.HermiteBand.isBand1_foPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:33:23.456706+00:00
-- url     : https://prove2.me/theorems/8f8e5e93-3345-4469-a6a4-6e1f5dd65400
-- title:
--   The Lean 4 theorem `isBand1_foPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand1_foPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand1_foPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand1_foPoly (b b' : Fin d → ℝ) : IsBand1 (BookProof.HermiteRelative.foPoly b b') := by sorry
