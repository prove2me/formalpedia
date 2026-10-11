-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_fderiv_fderiv_clmPow
-- name    : BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:19.893112+00:00
-- url     : https://prove2.me/theorems/33d68648-86f8-4dc4-9d0f-6986a86bed9c
-- title:
--   `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x v w : E) : fderiv ℝ (fderiv ℝ fun y => (ψ y) ^ k) x v w = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x v w : E) : fderiv ℝ (fderiv ℝ fun y => (ψ y) ^ k) x v w = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ψ v * ψ w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x v w : E) :
    fderiv ℝ (fderiv ℝ fun y => (ψ y) ^ k) x v w
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ψ v * ψ w := by sorry
