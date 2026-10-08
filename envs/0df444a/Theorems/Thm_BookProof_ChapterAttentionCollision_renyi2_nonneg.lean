-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_renyi2_nonneg
-- name    : BookProof.ChapterAttentionCollision.renyi2_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:22:33.456987+00:00
-- url     : https://prove2.me/theorems/4528a34c-3169-42df-9d3e-6a982f4c41c1
-- title:
--   `BookProof.ChapterAttentionCollision.renyi2_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : 0 ≤ renyi2 p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.renyi2_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : 0 ≤ renyi2 p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.renyi2_nonneg`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.renyi2_nonneg
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.renyi2_nonneg {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hsum : ∑ j, p j = 1) : 0 ≤ renyi2 p := by sorry
