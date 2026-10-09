-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_compose_isStochastic
-- name    : BookProof.ChapterAttentionMarkov.compose_isStochastic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:29.356354+00:00
-- url     : https://prove2.me/theorems/56866057-f9cd-4a49-a1dd-db961f0b20af
-- title:
--   `BookProof.ChapterAttentionMarkov.compose_isStochastic` {P Q : Fin m → Fin m → ℝ} (hP : IsStochastic P) (hQ : IsStochastic Q) : IsStochastic (compose P Q)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.compose_isStochastic` {P Q : Fin m → Fin m → ℝ} (hP : IsStochastic P) (hQ : IsStochastic Q) : IsStochastic (compose P Q)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.compose_isStochastic`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.compose_isStochastic
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.compose_isStochastic {P Q : Fin m → Fin m → ℝ} (hP : IsStochastic P)
    (hQ : IsStochastic Q) : IsStochastic (compose P Q) := by sorry
