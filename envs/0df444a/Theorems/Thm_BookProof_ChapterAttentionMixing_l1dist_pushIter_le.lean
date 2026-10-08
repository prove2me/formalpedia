-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_l1dist_pushIter_le
-- name    : BookProof.ChapterAttentionMixing.l1dist_pushIter_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:08:48.291694+00:00
-- url     : https://prove2.me/theorems/ac719d43-00e7-4cd9-9c26-bb58f7a7b9fc
-- title:
--   `BookProof.ChapterAttentionMixing.l1dist_pushIter_le` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : Is
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.l1dist_pushIter_le` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) (n : ℕ) : l1dist (pushIter P n p) (pushIter P n q) ≤ (1 - m * eps) ^ n * l1dist p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.l1dist_pushIter_le`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.l1dist_pushIter_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMarkov

variable {m : ℕ}

theorem BookProof.ChapterAttentionMixing.l1dist_pushIter_le {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q)
    (n : ℕ) :
    l1dist (pushIter P n p) (pushIter P n q) ≤ (1 - m * eps) ^ n * l1dist p q := by sorry
