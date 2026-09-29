-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand1_momPoly
-- name    : BookProof.HermiteBand.isBand1_momPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:33:34.243362+00:00
-- url     : https://prove2.me/theorems/356bf01f-a376-460d-b999-2af434f9f7cc
-- title:
--   The Lean 4 theorem `isBand1_momPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand1_momPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand1_momPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand1_momPoly (i : Fin d) : IsBand1 (momPoly i) := by sorry
