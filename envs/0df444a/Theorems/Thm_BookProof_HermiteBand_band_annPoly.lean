-- Prove2me | Theorems.Thm_BookProof_HermiteBand_band_annPoly
-- name    : BookProof.HermiteBand.band_annPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:04:06.948754+00:00
-- url     : https://prove2.me/theorems/f2268222-ebe6-4414-9cdc-94e1c96ee479
-- title:
--   The Lean 4 theorem `band_annPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `band_annPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.band_annPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.band_annPoly (i : Fin d) : Band (annPoly i) 1 1 1 g1 := by sorry
