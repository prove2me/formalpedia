-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_le_crossEntropy
-- name    : BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:37.550989+00:00
-- url     : https://prove2.me/theorems/b736508f-a365-4457-af6c-39775d3e555d
-- title:
--   `BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy` {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : shan
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxMaxEntropy`.
--
--   `BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy` {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) : shannonEntropy p ≤ crossEntropy p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy`.

-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy {p q : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hpsum : ∑ j, p j = 1) (hq0 : ∀ j, 0 < q j) (hqsum : ∑ j, q j ≤ 1) :
    shannonEntropy p ≤ crossEntropy p q := by sorry
