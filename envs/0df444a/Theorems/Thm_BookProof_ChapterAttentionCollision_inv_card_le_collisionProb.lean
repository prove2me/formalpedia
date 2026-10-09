-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_inv_card_le_collisionProb
-- name    : BookProof.ChapterAttentionCollision.inv_card_le_collisionProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:21:11.798986+00:00
-- url     : https://prove2.me/theorems/a976fdf6-0fa9-4974-ada3-93557d8c94ba
-- title:
--   `BookProof.ChapterAttentionCollision.inv_card_le_collisionProb` {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) : (m : ℝ)⁻¹ ≤ collisionProb p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.inv_card_le_collisionProb` {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) : (m : ℝ)⁻¹ ≤ collisionProb p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.inv_card_le_collisionProb`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.inv_card_le_collisionProb
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.inv_card_le_collisionProb {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) :
    (m : ℝ)⁻¹ ≤ collisionProb p := by sorry
