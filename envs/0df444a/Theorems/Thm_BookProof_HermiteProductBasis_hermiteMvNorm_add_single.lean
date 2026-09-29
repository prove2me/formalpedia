-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_add_single
-- name    : BookProof.HermiteProductBasis.hermiteMvNorm_add_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:06.817414+00:00
-- url     : https://prove2.me/theorems/7a41b42e-890b-4877-9e83-60f5320c48d3
-- title:
--   The Lean 4 theorem `hermiteMvNorm_add_single` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteMvNorm_add_single` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.hermiteMvNorm_add_single
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.hermiteMvNorm_add_single (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + Finsupp.single i 1) = hermiteMvNorm a * Real.sqrt ((a i : ℝ) + 1) := by sorry
