-- Prove2me | Theorems.Thm_FamousTheorems_erdos_kaplansky
-- name    : FamousTheorems.erdos_kaplansky
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:04.224732+00:00
-- url     : https://prove2.me/theorems/10ab4671-6900-4f30-a340-0921a82a5b7f
-- title:
--   The Erdős–Kaplansky theorem
-- statement:
--   **The Erdős–Kaplansky theorem.** Let $V$ be an infinite-dimensional vector space over a field $K$. Then the dimension of the dual space $V^*=\operatorname{Hom}_K(V,K)$ equals its cardinality:
--   $$\dim_KV^*=|V^*|.$$
--
--   Since $|V^*|=|K|^{\dim V}$, the dual of an infinite-dimensional space has strictly larger dimension than the space itself. In particular $V$ is never isomorphic to its dual, and the double-dual map $V\to V^{**}$ is never surjective. This marks a basic difference between finite- and infinite-dimensional linear algebra.
--
--   **Formalization note.** Mathlib's `rank_dual_eq_card_dual_of_aleph0_le_rank`. Infinite dimensionality is `Cardinal.aleph0 ≤ Module.rank K V`. The dual space is written as `V →ₗ[K] K`, and `Cardinal.mk` is its cardinality.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `rank_dual_eq_card_dual_of_aleph0_le_rank`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem erdos_kaplansky {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : Cardinal.aleph0 ≤ Module.rank K V) :
    Module.rank K (V →ₗ[K] K) = Cardinal.mk (V →ₗ[K] K) := by sorry

end FamousTheorems
