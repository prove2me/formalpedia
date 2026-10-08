-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_tendsto_l1dist_pushIter
-- name    : BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:09:06.718004+00:00
-- url     : https://prove2.me/theorems/b025c31c-d495-474a-9f7c-c92c5e59a276
-- title:
--   `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) (hpos : 0 < eps) (i : Fin m) : Tendsto (fun n => l1dist (pushIter P n p) (pushIter P n q)) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter
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

theorem BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q)
    (hpos : 0 < eps) (i : Fin m) :
    Tendsto (fun n => l1dist (pushIter P n p) (pushIter P n q)) atTop (𝓝 0) := by sorry
