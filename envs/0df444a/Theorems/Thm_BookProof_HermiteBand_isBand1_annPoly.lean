-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand1_annPoly
-- name    : BookProof.HermiteBand.isBand1_annPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:28:07.187423+00:00
-- url     : https://prove2.me/theorems/d4247da3-f05f-4a9d-9ccc-e7aa4c84f35d
-- title:
--   The Lean 4 theorem `isBand1_annPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand1_annPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand1_annPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand1_annPoly (i : Fin d) : IsBand1 (annPoly i) := by sorry
