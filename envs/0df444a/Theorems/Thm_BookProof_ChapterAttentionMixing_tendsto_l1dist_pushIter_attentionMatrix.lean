-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_tendsto_l1dist_pushIter_attentionMatrix
-- name    : BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:09:32.301077+00:00
-- url     : https://prove2.me/theorems/9d3001b5-20a9-4a85-986f-f1a442d1aa67
-- title:
--   `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix` {beta D : ℝ} (hb : 0 ≤ beta) {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q) (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix` {beta D : ℝ} (hb : 0 ≤ beta) {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q) (hD : ∀ i j l, S i l ≤ S i j + D) (i : Fin m) : Tendsto (fun n => l1dist (pushIter (attentionMatrix beta S) n p) (pushIter (attentionMatrix beta S) n q)) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix
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

theorem BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix {beta D : ℝ} (hb : 0 ≤ beta)
    {S : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} (hp : IsProb p) (hq : IsProb q)
    (hD : ∀ i j l, S i l ≤ S i j + D) (i : Fin m) :
    Tendsto (fun n => l1dist (pushIter (attentionMatrix beta S) n p)
      (pushIter (attentionMatrix beta S) n q)) atTop (𝓝 0) := by sorry
