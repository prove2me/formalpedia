-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_mem_causalMask
-- name    : BookProof.ChapterAttentionMasking.mem_causalMask
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:30:29.554365+00:00
-- url     : https://prove2.me/theorems/582d7c7f-4af6-4c2f-8b8a-563806537fb9
-- title:
--   `BookProof.ChapterAttentionMasking.mem_causalMask` {i l : Fin m} : l ∈ causalMask m i ↔ l ≤ i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.mem_causalMask` {i l : Fin m} : l ∈ causalMask m i ↔ l ≤ i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.mem_causalMask`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.mem_causalMask
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.mem_causalMask {i l : Fin m} : l ∈ causalMask m i ↔ l ≤ i := by sorry
