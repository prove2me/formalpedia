-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand2_fqPoly
-- name    : BookProof.HermiteBand.isBand2_fqPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:34:39.00096+00:00
-- url     : https://prove2.me/theorems/4a82a12f-9ee3-4770-b69b-de62fd5d9957
-- title:
--   The Lean 4 theorem `isBand2_fqPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand2_fqPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand2_fqPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand2_fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    IsBand2 (fqPoly P Q S b b') := by sorry
