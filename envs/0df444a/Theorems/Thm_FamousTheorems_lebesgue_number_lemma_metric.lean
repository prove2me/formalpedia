-- Prove2me | Theorems.Thm_FamousTheorems_lebesgue_number_lemma_metric
-- name    : FamousTheorems.lebesgue_number_lemma_metric
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:23.959952+00:00
-- url     : https://prove2.me/theorems/c8c56264-896f-4841-957d-eb103f772490
-- title:
--   The Lebesgue number lemma
-- statement:
--   **The Lebesgue number lemma.** Let $s$ be a compact subset of a (pseudo)metric space, covered by a family of open sets $(c_i)$. Then there is $\delta>0$ such that for every $x\in s$ the ball $B(x,\delta)$ is contained in a single $c_i$.
--
--   Such a $\delta$ is called a Lebesgue number of the cover. The lemma is used to prove uniform continuity of continuous functions on compact sets and in simplicial approximation and path-lifting arguments in algebraic topology.
--
--   **Formalization note.** Mathlib's `lebesgue_number_lemma_of_metric`. The index type is an arbitrary `Sort`, and the conclusion is `∃ δ > 0, ∀ x ∈ s, ∃ i, Metric.ball x δ ⊆ c i`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `lebesgue_number_lemma_of_metric`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lebesgue_number_lemma_metric {α : Type*} [PseudoMetricSpace α] {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, Metric.ball x δ ⊆ c i := by sorry

end FamousTheorems
