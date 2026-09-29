-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand1_mulXPoly
-- name    : BookProof.HermiteBand.isBand1_mulXPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:34:22.893024+00:00
-- url     : https://prove2.me/theorems/7ddf4aa0-ac22-454b-8c35-c4c4b131d716
-- title:
--   The Lean 4 theorem `isBand1_mulXPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand1_mulXPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand1_mulXPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand1_mulXPoly (i : Fin d) : IsBand1 (mulXPoly i) := by sorry
