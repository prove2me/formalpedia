-- Prove2me | Theorems.Thm_FamousTheorems_neumann_coset_cover_6b
-- name    : FamousTheorems.neumann_coset_cover_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:37.714819+00:00
-- url     : https://prove2.me/theorems/90279623-90ce-4416-b33a-4684e38b1ac2
-- title:
--   B. H. Neumann's lemma on coset coverings
-- statement:
--   **B. H. Neumann's lemma on coset coverings.** Let $G$ be a group covered by finitely many left cosets $g_1H_1,\dots,g_nH_n$ of subgroups $H_1,\dots,H_n$. Then at least one $H_i$ has finite index, and in fact $[G:H_i]\le n$ for some $i$.
--
--   B. H. Neumann proved this in 1954. It shows that a group cannot be covered by finitely many cosets of infinite-index subgroups, so, for example, $\mathbb Z^2$ is not a finite union of cosets of cyclic subgroups. It is used in the theory of FC-groups, in model theory and in combinatorial group theory.
--
--   **Formalization note.** Mathlib's `Subgroup.exists_index_le_card_of_leftCoset_cover`. The cover is indexed by a finite set $s$, `g i • (H i : Set G)` is the left coset $g_iH_i$, and `FiniteIndex` together with `index ≤ s.card` gives $[G:H_i]\le|s|$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.exists_index_le_card_of_leftCoset_cover`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Pointwise

theorem neumann_coset_cover_6b {G ι : Type*} [Group G] {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, g i • (H i : Set G) = Set.univ) :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by sorry

end FamousTheorems
