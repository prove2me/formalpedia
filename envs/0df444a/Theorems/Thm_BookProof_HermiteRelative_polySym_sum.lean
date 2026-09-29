-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_polySym_sum
-- name    : BookProof.HermiteRelative.polySym_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:17:56.068695+00:00
-- url     : https://prove2.me/theorems/a8906346-7e34-4cf7-8703-24812f3144e9
-- title:
--   The Lean 4 theorem `polySym_sum` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polySym_sum` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.polySym_sum
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

theorem BookProof.HermiteRelative.polySym_sum {ι : Type*} (s : Finset ι)
    (T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by sorry
