-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_causalMask_subset
-- name    : BookProof.ChapterAttentionMasking.causalMask_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:30:51.952261+00:00
-- url     : https://prove2.me/theorems/9389a46a-2431-480d-8f3c-3ec742adf906
-- title:
--   `BookProof.ChapterAttentionMasking.causalMask_subset` {i i' : Fin m} (h : i ≤ i') : causalMask m i ⊆ causalMask m i'
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.causalMask_subset` {i i' : Fin m} (h : i ≤ i') : causalMask m i ⊆ causalMask m i'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.causalMask_subset`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.causalMask_subset
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.causalMask_subset {i i' : Fin m} (h : i ≤ i') : causalMask m i ⊆ causalMask m i' := by sorry
