-- Prove2me | Theorems.Thm_FamousTheorems_szemeredi_regularity_lemma
-- name    : FamousTheorems.szemeredi_regularity_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:55.65499+00:00
-- url     : https://prove2.me/theorems/65905be0-cae3-479a-b899-6207649497a6
-- title:
--   The Szemerédi regularity lemma
-- statement:
--   **The Szemerédi regularity lemma.** For every $\varepsilon>0$ and every $l\in\mathbb N$ there is $M$ such that every finite graph $G$ with at least $l$ vertices has an equipartition of its vertex set into $k$ parts, $l\le k\le M$, that is $\varepsilon$-uniform (all but at most an $\varepsilon$ fraction of the pairs of parts are $\varepsilon$-regular).
--
--   The bound $M$ depends only on $\varepsilon$ and $l$, not on the graph. So every large graph is approximated, up to $\varepsilon$, by a bounded-size weighted "reduced" graph. The lemma is a central tool of extremal graph theory and additive combinatorics, used in the proofs of Szemerédi's theorem, the triangle removal lemma and the Erdős–Stone theorem.
--
--   **Formalization note.** Derived from Mathlib's `szemeredi_regularity`, whose explicit tower-type bound is `SzemerediRegularity.bound ε l`. `Finpartition.IsEquipartition` means the parts differ in size by at most one, and `Finpartition.IsUniform G ε` is Mathlib's notion of $\varepsilon$-uniform partition, based on `SimpleGraph.IsUniform` for pairs of parts. The quantification over all finite vertex types is uniform in the bound $M$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `szemeredi_regularity`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem szemeredi_regularity_lemma {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    ∃ M : ℕ, ∀ (α : Type*) [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj],
      l ≤ Fintype.card α → ∃ P : Finpartition (Finset.univ : Finset α),
        P.IsEquipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ M ∧ P.IsUniform G ε := by sorry

end FamousTheorems
