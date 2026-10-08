-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_shannonEntropy_nonneg
-- name    : BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:55:28.912205+00:00
-- url     : https://prove2.me/theorems/26cf94d1-67db-4f4d-ad52-6e92b9e630ea
-- title:
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) : 0 ≤ shannonEntropy p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) : 0 ≤ shannonEntropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    0 ≤ shannonEntropy p := by sorry
