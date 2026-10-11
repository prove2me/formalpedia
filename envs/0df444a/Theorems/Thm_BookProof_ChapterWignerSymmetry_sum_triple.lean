-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_triple
-- name    : BookProof.ChapterWignerSymmetry.sum_triple
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:21:18.873911+00:00
-- url     : https://prove2.me/theorems/da73c4d2-0368-4840-85b3-8dc80dcf0589
-- title:
--   `BookProof.ChapterWignerSymmetry.sum_triple` {o i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) {f : ι → ℂ} (hf : ∀ k, k ≠ o → k ≠ i → k ≠ j → f k = 0) (g : ι →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.sum_triple` {o i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) {f : ι → ℂ} (hf : ∀ k, k ≠ o → k ≠ i → k ≠ j → f k = 0) (g : ι → ℂ) : ∑ k, g k * f k = g o * f o + g i * f i + g j * f j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.sum_triple`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.sum_triple
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BookProof.ChapterWignerSymmetry.sum_triple {o i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) {f : ι → ℂ}
    (hf : ∀ k, k ≠ o → k ≠ i → k ≠ j → f k = 0) (g : ι → ℂ) :
    ∑ k, g k * f k = g o * f o + g i * f i + g j * f j := by sorry
