-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_hermiteNorm_succ
-- name    : BookProof.HermiteProductBasis.hermiteNorm_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:47:55.767799+00:00
-- url     : https://prove2.me/theorems/9df139b1-c790-4c74-a7ec-f70c5324bc00
-- title:
--   The Lean 4 theorem `hermiteNorm_succ` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteNorm_succ` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.hermiteNorm_succ
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.hermiteNorm_succ (n : ℕ) :
    hermiteNorm (n + 1) = hermiteNorm n * Real.sqrt ((n : ℝ) + 1) := by sorry
