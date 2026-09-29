-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvNorm_sub_single
-- name    : BookProof.HermiteProductBasis.hermiteMvNorm_sub_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:17:17.319978+00:00
-- url     : https://prove2.me/theorems/98f3cd98-69c8-4c90-8810-ca871f492362
-- title:
--   The Lean 4 theorem `hermiteMvNorm_sub_single` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteMvNorm_sub_single` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.hermiteMvNorm_sub_single
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.hermiteMvNorm_sub_single {i : Fin d} {a : Fin d →₀ ℕ} (h : 1 ≤ a i) :
    hermiteMvNorm a = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) := by sorry
