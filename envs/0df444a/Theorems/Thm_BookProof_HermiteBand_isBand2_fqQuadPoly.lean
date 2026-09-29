-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand2_fqQuadPoly
-- name    : BookProof.HermiteBand.isBand2_fqQuadPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:34:45.935703+00:00
-- url     : https://prove2.me/theorems/22c35bbb-19fd-477b-a5bb-b16e7fc18a60
-- title:
--   The Lean 4 theorem `isBand2_fqQuadPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand2_fqQuadPoly` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand2_fqQuadPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand2_fqQuadPoly (P Q S : Fin d → Fin d → ℝ) : IsBand2 (fqQuadPoly P Q S) := by sorry
