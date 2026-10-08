-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_push_attentionMatrix_le
-- name    : BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:42.865466+00:00
-- url     : https://prove2.me/theorems/7b421080-dc15-4cc8-89b3-2ac66ef32a03
-- title:
--   `BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le` {beta D : ℝ} (hb : 0 ≤ beta) {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q) (hD : ∀ i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le` {beta D : ℝ} (hb : 0 ≤ beta) {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q) (hD : ∀ i j l, S i l ≤ S i j + D) : l1dist (push (attentionMatrix beta S) p) (push (attentionMatrix beta S) q) ≤ (1 - Real.exp (-(beta * D))) * l1dist p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le {beta D : ℝ} (hb : 0 ≤ beta)
    {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hD : ∀ i j l, S i l ≤ S i j + D) :
    l1dist (push (attentionMatrix beta S) p) (push (attentionMatrix beta S) q)
      ≤ (1 - Real.exp (-(beta * D))) * l1dist p q := by sorry
