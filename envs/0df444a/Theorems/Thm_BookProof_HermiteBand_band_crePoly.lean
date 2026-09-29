-- Prove2me | Theorems.Thm_BookProof_HermiteBand_band_crePoly
-- name    : BookProof.HermiteBand.band_crePoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:04:40.204956+00:00
-- url     : https://prove2.me/theorems/820d986e-e051-4451-a67d-1a2fceb81706
-- title:
--   The Lean 4 theorem `band_crePoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `band_crePoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.band_crePoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.band_crePoly (i : Fin d) : Band (crePoly i) 1 1 1 g1 := by sorry
