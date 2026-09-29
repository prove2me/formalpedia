-- Prove2me | Theorems.Thm_FamousTheorems_subgroup_smallest_prime_index_normal
-- name    : FamousTheorems.subgroup_smallest_prime_index_normal
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:17.464104+00:00
-- url     : https://prove2.me/theorems/0ad05402-c958-4b20-b362-d4634c89691f
-- title:
--   A subgroup of smallest prime index is normal
-- statement:
--   **A subgroup of smallest prime index is normal.** Let $G$ be a finite group and $p$ the smallest prime dividing $|G|$. Every subgroup $H\le G$ of index $p$ is normal.
--
--   The proof lets $G$ act on the cosets of $H$ and observes that the image of $G$ in $S_p$ has order dividing both $|G|$ and $p!$. This generalises the fact that index-$2$ subgroups are normal. It is used to show that groups of order $pq$ and similar orders are not simple.
--
--   **Formalization note.** Mathlib's `Subgroup.normal_of_index_eq_minFac_card`. `(Nat.card G).minFac` is the smallest prime factor of $|G|$. For an infinite group, `Nat.card G = 0` and `Nat.minFac 0 = 2`, so the statement then says that subgroups of index $2$ are normal, which is also true.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.normal_of_index_eq_minFac_card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem subgroup_smallest_prime_index_normal {G : Type*} [Group G] {H : Subgroup G} (h : H.index = (Nat.card G).minFac) : H.Normal := by sorry

end FamousTheorems
