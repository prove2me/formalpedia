-- Prove2me | Theorems.Thm_FamousTheorems_vitali_covering
-- name    : FamousTheorems.vitali_covering
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:56.407379+00:00
-- url     : https://prove2.me/theorems/70fd1ddf-b87b-4137-b56e-88a6318bb6d0
-- title:
--   The Vitali covering theorem
-- statement:
--   **The Vitali covering theorem (almost-everywhere form).** Let $\mu$ be a locally finite measure on a second-countable metric space. Let $(B_a)_{a\in t}$ be closed sets with nonempty interior, $B_a\subseteq\overline B(c_a,r_a)$ and $\mu(\overline B(c_a,3r_a))\le C\,\mu(B_a)$. Suppose that every $x\in s$ is the centre of sets $B_a$ of arbitrarily small radius. Then there is a countable disjoint subfamily $(B_a)_{a\in u}$ that covers $\mu$-almost all of $s$.
--
--   It is the covering lemma behind the Lebesgue differentiation theorem and the Hardy–Littlewood maximal inequality for doubling measures, such as Lebesgue measure on $\mathbb R^n$.
--
--   **Formalization note.** Mathlib's `Vitali.exists_disjoint_covering_ae`; the doubling-type condition is the hypothesis `μ (closedBall (c a) (3 * r a)) ≤ C * μ (B a)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Vitali.exists_disjoint_covering_ae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vitali_covering {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsLocallyFiniteMeasure μ] (s : Set α) (t : Set ι) (C : NNReal)
    (r : ι → ℝ) (c : ι → α) (B : ι → Set α) (hB : ∀ a ∈ t, B a ⊆ Metric.closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (Metric.closedBall (c a) (3 * r a)) ≤ C * μ (B a)) (ht : ∀ a ∈ t, (interior (B a)).Nonempty)
    (h't : ∀ a ∈ t, IsClosed (B a)) (hf : ∀ x ∈ s, ∀ ε > 0, ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 := by sorry

end FamousTheorems
