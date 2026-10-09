-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_push_compose
-- name    : BookProof.ChapterAttentionMarkov.push_compose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:03.94374+00:00
-- url     : https://prove2.me/theorems/54fb74e0-c4a9-4908-b8de-6e885aeb08f9
-- title:
--   `BookProof.ChapterAttentionMarkov.push_compose` (P Q : Fin m → Fin m → ℝ) (p : Fin m → ℝ) (j : Fin m) : push (compose P Q) p j = push Q (push P p) j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.push_compose` (P Q : Fin m → Fin m → ℝ) (p : Fin m → ℝ) (j : Fin m) : push (compose P Q) p j = push Q (push P p) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.push_compose`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.push_compose
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.push_compose (P Q : Fin m → Fin m → ℝ) (p : Fin m → ℝ) (j : Fin m) :
    push (compose P Q) p j = push Q (push P p) j := by sorry
