-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_pair_prime
-- name    : BookProof.ChapterWignerSymmetry.sum_pair_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:52.611984+00:00
-- url     : https://prove2.me/theorems/03136e4d-6c38-4fab-aec8-17405fda08be
-- title:
--   BookProof.ChapterWignerSymmetry.sum_pair'
-- statement:
--   BookProof.ChapterWignerSymmetry.sum_pair'

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.sum_pair'
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BookProof.ChapterWignerSymmetry.sum_pair_prime {o i : ι} (hi : i ≠ o) {f : ι → ℂ} (hf : ∀ k, k ≠ o → k ≠ i → f k = 0)
    (g : ι → ℂ) : ∑ k, g k * f k = g o * f o + g i * f i := by sorry
