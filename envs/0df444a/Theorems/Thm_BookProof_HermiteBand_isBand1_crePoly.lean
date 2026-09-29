-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand1_crePoly
-- name    : BookProof.HermiteBand.isBand1_crePoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:28:18.381988+00:00
-- url     : https://prove2.me/theorems/5ab3d11b-c94c-4173-9416-237cec89c1c2
-- title:
--   The Lean 4 theorem `isBand1_crePoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand1_crePoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand1_crePoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand1_crePoly (i : Fin d) : IsBand1 (crePoly i) := by sorry
