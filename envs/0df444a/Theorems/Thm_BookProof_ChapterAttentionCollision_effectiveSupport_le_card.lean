-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_effectiveSupport_le_card
-- name    : BookProof.ChapterAttentionCollision.effectiveSupport_le_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:21:38.091893+00:00
-- url     : https://prove2.me/theorems/5fb617cb-15ef-4550-9fb6-06631d9d23c5
-- title:
--   `BookProof.ChapterAttentionCollision.effectiveSupport_le_card` {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) : effectiveSupport p ≤ (m : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.effectiveSupport_le_card` {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) : effectiveSupport p ≤ (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.effectiveSupport_le_card`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.effectiveSupport_le_card
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.effectiveSupport_le_card {p : Fin m → ℝ} (hsum : ∑ j, p j = 1) :
    effectiveSupport p ≤ (m : ℝ) := by sorry
