-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_nonneg
-- name    : BookProof.ChapterAttentionMarkov.l1dist_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:06.038728+00:00
-- url     : https://prove2.me/theorems/a1b022e4-0024-4583-bd98-4fa94286a56f
-- title:
--   `BookProof.ChapterAttentionMarkov.l1dist_nonneg` (p q : Fin m → ℝ) : 0 ≤ l1dist p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.l1dist_nonneg` (p q : Fin m → ℝ) : 0 ≤ l1dist p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.l1dist_nonneg`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.l1dist_nonneg
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.l1dist_nonneg (p q : Fin m → ℝ) : 0 ≤ l1dist p q := by sorry
