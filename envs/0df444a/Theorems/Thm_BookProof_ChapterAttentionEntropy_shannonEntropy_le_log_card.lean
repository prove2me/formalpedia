-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_shannonEntropy_le_log_card
-- name    : BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:55:26.198611+00:00
-- url     : https://prove2.me/theorems/04395b0a-05c0-4b33-af8f-67bd08d53245
-- title:
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) : shannonEntropy p ≤ Real.log m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) : shannonEntropy p ≤ Real.log m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterAttentionEntropy.shannonEntropy_le_log_card {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) : shannonEntropy p ≤ Real.log m := by sorry
