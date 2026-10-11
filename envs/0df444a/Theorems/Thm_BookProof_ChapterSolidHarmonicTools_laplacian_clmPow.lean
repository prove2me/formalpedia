-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_clmPow
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:30.652985+00:00
-- url     : https://prove2.me/theorems/f9eddf33-36f8-4a31-b6d5-5acb7947f4ae
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) : (Δ fun y => (ψ y) ^ k) x = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ∑ i, (ψ (stdOrthonor
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) : (Δ fun y => (ψ y) ^ k) x = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ∑ i, (ψ (stdOrthonormalBasis ℝ E i)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_clmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.laplacian_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    (Δ fun y => (ψ y) ^ k) x
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2)
          * ∑ i, (ψ (stdOrthonormalBasis ℝ E i)) ^ 2 := by sorry
