-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_collisionProb_uniform
-- name    : BookProof.ChapterAttentionCollision.collisionProb_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:22:06.155554+00:00
-- url     : https://prove2.me/theorems/0b33fca2-bdc1-4c26-83ab-d4206237588d
-- title:
--   `BookProof.ChapterAttentionCollision.collisionProb_uniform` (hm : 0 < m) : collisionProb (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.collisionProb_uniform` (hm : 0 < m) : collisionProb (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.collisionProb_uniform`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.collisionProb_uniform
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.collisionProb_uniform (hm : 0 < m) :
    collisionProb (fun _ : Fin m => (1 : ℝ) / m) = (m : ℝ)⁻¹ := by sorry
