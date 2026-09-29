-- Prove2me | Theorems.Thm_BookProof_HermiteBand_annPoly_hpsi
-- name    : BookProof.HermiteBand.annPoly_hpsi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T11:59:37.134135+00:00
-- url     : https://prove2.me/theorems/a233a6b5-c241-4c1e-b018-63b0fcc2d9e9
-- title:
--   The Lean 4 theorem `annPoly_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `annPoly_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.annPoly_hpsi
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.annPoly_hpsi (i : Fin d) (α : Fin d →₀ ℕ) :
    annPoly i (hpsi α) = ((Real.sqrt (α i : ℝ) : ℝ) : ℂ) • hpsi (α - Finsupp.single i 1) := by sorry
