-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_push_le
-- name    : BookProof.ChapterAttentionMarkov.l1dist_push_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:11.920822+00:00
-- url     : https://prove2.me/theorems/78a3978c-6c62-4bd0-831e-8a9b83776aba
-- title:
--   `BookProof.ChapterAttentionMarkov.l1dist_push_le` {P : Fin m → Fin m → ℝ} (hP : IsStochastic P) (p q : Fin m → ℝ) : l1dist (push P p) (push P q) ≤ l1dist p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.l1dist_push_le` {P : Fin m → Fin m → ℝ} (hP : IsStochastic P) (p q : Fin m → ℝ) : l1dist (push P p) (push P q) ≤ l1dist p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.l1dist_push_le`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.l1dist_push_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.l1dist_push_le {P : Fin m → Fin m → ℝ} (hP : IsStochastic P) (p q : Fin m → ℝ) :
    l1dist (push P p) (push P q) ≤ l1dist p q := by sorry
