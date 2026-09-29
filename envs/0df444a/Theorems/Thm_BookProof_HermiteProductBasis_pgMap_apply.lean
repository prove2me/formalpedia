-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pgMap_apply
-- name    : BookProof.HermiteProductBasis.pgMap_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:34.820579+00:00
-- url     : https://prove2.me/theorems/f12b6c75-186f-4758-808e-8b16a73ea8a5
-- title:
--   The Lean 4 theorem `pgMap_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgMap_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pgMap_apply
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pgMap_apply (p : MvPolynomial (Fin d) ℂ) : pgMap p = pgLp p := by sorry
