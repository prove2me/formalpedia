-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLocality_scoreSoftmax_alibi_le
-- name    : BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:26:18.97098+00:00
-- url     : https://prove2.me/theorems/173ffbcc-4e04-4937-88e4-883b038d71ba
-- title:
--   `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le` {beta gamma Delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0) (hDelta : ∀ l, s l ≤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLocality`.
--
--   `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le` {beta gamma Delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0) (hDelta : ∀ l, s l ≤ s j₀ + Delta) (l : Fin m) : scoreSoftmax beta (alibiScore s gamma d) l ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le`.

-- Generated from ChapterAttentionLocality.lean — theorem BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionLocality


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le {beta gamma Delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0) (hDelta : ∀ l, s l ≤ s j₀ + Delta)
    (l : Fin m) :
    scoreSoftmax beta (alibiScore s gamma d) l
      ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l))) := by sorry
