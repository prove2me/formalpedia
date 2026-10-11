-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_supported
-- name    : BookProof.ChapterWignerSymmetry.sum_supported
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:23.902974+00:00
-- url     : https://prove2.me/theorems/ba25ccd2-10f4-47dc-b0e2-7d91b6cbf882
-- title:
--   `BookProof.ChapterWignerSymmetry.sum_supported` {s : Finset ι} {f : ι → ℂ} (hf : ∀ k, k ∉ s → f k = 0) (g : ι → ℂ) : ∑ k, g k * f k = ∑ k ∈ s, g k * f k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.sum_supported` {s : Finset ι} {f : ι → ℂ} (hf : ∀ k, k ∉ s → f k = 0) (g : ι → ℂ) : ∑ k, g k * f k = ∑ k ∈ s, g k * f k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.sum_supported`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.sum_supported
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BookProof.ChapterWignerSymmetry.sum_supported {s : Finset ι} {f : ι → ℂ} (hf : ∀ k, k ∉ s → f k = 0) (g : ι → ℂ) :
    ∑ k, g k * f k = ∑ k ∈ s, g k * f k := by sorry
