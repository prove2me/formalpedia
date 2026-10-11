-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_clmPow
-- name    : BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:37.175416+00:00
-- url     : https://prove2.me/theorems/4c1589d5-bbfb-4693-8477-ed2dbdc9246c
-- title:
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) : HasFDerivAt (fun y => (ψ y) ^ k) (((k : ℂ) * (ψ x) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ)) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) : HasFDerivAt (fun y => (ψ y) ^ k) (((k : ℂ) * (ψ x) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (ψ y) ^ k) (((k : ℂ) * (ψ x) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ)) x := by sorry
