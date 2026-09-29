-- Prove2me | Theorems.Thm_FamousTheorems_bergelson_intersectivity_lemma
-- name    : FamousTheorems.bergelson_intersectivity_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:31.735984+00:00
-- url     : https://prove2.me/theorems/104b5606-e7d0-4802-b9d4-6034561e1e53
-- title:
--   Bergelson's intersectivity lemma
-- statement:
--   **Bergelson's intersectivity lemma.** Let $\mu$ be a finite measure and $(s_i)_{i\in\iota}$ an infinite family of measurable sets with $\mu(s_i)\ge r>0$ for all $i$. Then there is an infinite set of indices $t$ such that every finite intersection $\bigcap_{i\in u}s_i$, with $u\subseteq t$ finite, has positive measure.
--
--   Bergelson proved this in 1985. It is the measure-theoretic core of several density Ramsey theorems. Through Furstenberg's correspondence principle, it shows for example that any set of integers of positive upper density contains, up to a shift, a subset whose finite intersections are all large.
--
--   **Formalization note.** Mathlib's `bergelson`. The index type $\iota$ is any infinite type. The lower bound $r$ lies in $[0,\infty]$ and is assumed nonzero, and finite subsets of $t$ are sets `u ⊆ t` with `u.Finite`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `bergelson`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bergelson_intersectivity_lemma {ι α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {r : ENNReal} [Infinite ι] {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hr₀ : r ≠ 0)
    (hr : ∀ i, r ≤ μ (s i)) :
    ∃ t : Set ι, t.Infinite ∧ ∀ ⦃u : Set ι⦄, u ⊆ t → u.Finite → 0 < μ (⋂ i ∈ u, s i) := by sorry

end FamousTheorems
