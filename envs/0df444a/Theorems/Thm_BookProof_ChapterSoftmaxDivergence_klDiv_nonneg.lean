-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxDivergence_klDiv_nonneg
-- name    : BookProof.ChapterSoftmaxDivergence.klDiv_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:31.948487+00:00
-- url     : https://prove2.me/theorems/0aee3de5-2935-4f59-9699-c15c933a68b5
-- title:
--   `BookProof.ChapterSoftmaxDivergence.klDiv_nonneg` {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : 0 ≤ klDiv p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxDivergence`.
--
--   `BookProof.ChapterSoftmaxDivergence.klDiv_nonneg` {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : 0 ≤ klDiv p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxDivergence.klDiv_nonneg`.

-- Generated from ChapterSoftmaxDivergence.lean — theorem BookProof.ChapterSoftmaxDivergence.klDiv_nonneg
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
open BookProof.ChapterSoftmaxDivergence


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxDivergence.klDiv_nonneg {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : 0 ≤ klDiv p q := by sorry
