-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_polySym_foPoly
-- name    : BookProof.HermiteRelative.polySym_foPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:04.49834+00:00
-- url     : https://prove2.me/theorems/ea23f123-d37e-43de-834b-d0afe55a027d
-- title:
--   The Lean 4 theorem `polySym_foPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polySym_foPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.polySym_foPoly
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

theorem BookProof.HermiteRelative.polySym_foPoly (b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (foPoly b b') := by sorry
