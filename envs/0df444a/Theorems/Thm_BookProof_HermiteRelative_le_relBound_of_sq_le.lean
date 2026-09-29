-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_le_relBound_of_sq_le
-- name    : BookProof.HermiteRelative.le_relBound_of_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:49:27.231817+00:00
-- url     : https://prove2.me/theorems/3c5db5fb-bdb5-4e3c-8a3f-cb165f90ac81
-- title:
--   The Lean 4 theorem `le_relBound_of_sq_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `le_relBound_of_sq_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.le_relBound_of_sq_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

theorem BookProof.HermiteRelative.le_relBound_of_sq_le {t A B c0 e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc0 : 0 < c0) (he : 0 < e) (h : t ^ 2 ≤ (4 / c0) * (B * A)) :
    t ≤ e * A + (2 / (c0 * e)) * B := by sorry
