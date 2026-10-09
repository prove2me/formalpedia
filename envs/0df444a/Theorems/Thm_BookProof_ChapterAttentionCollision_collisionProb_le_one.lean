-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_le_one
-- name    : BookProof.ChapterAttentionCollision.collisionProb_le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:21:02.402988+00:00
-- url     : https://prove2.me/theorems/813f9a82-e89b-48aa-bf76-e0f0b74288d4
-- title:
--   `BookProof.ChapterAttentionCollision.collisionProb_le_one` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : collisionProb p ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.collisionProb_le_one` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : collisionProb p ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.collisionProb_le_one`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.collisionProb_le_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.collisionProb_le_one {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hsum : ∑ j, p j = 1) : collisionProb p ≤ 1 := by sorry
