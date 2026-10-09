-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_one_le_effectiveSupport
-- name    : BookProof.ChapterAttentionCollision.one_le_effectiveSupport
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:21:33.134459+00:00
-- url     : https://prove2.me/theorems/191102d3-760d-436b-95fd-73785a7e9594
-- title:
--   `BookProof.ChapterAttentionCollision.one_le_effectiveSupport` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : 1 ≤ effectiveSupport p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.one_le_effectiveSupport` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (hsum : ∑ j, p j = 1) : 1 ≤ effectiveSupport p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.one_le_effectiveSupport`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.one_le_effectiveSupport
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.one_le_effectiveSupport {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hsum : ∑ j, p j = 1) : 1 ≤ effectiveSupport p := by sorry
