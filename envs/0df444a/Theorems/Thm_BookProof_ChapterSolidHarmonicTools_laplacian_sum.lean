-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_sum
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:56:34.498985+00:00
-- url     : https://prove2.me/theorems/1b6e9d98-ba4a-4649-837d-7c131f0e437f
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_sum` {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) : (Δ fun y => ∑ i ∈ s, f i y) x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_sum` {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) : (Δ fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, (Δ (f i)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_sum`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_sum
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

theorem BookProof.ChapterSolidHarmonicTools.laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    (Δ fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, (Δ (f i)) x := by sorry
