-- Prove2me | Theorems.Thm_FamousTheorems_perm_order_lcm_cycle_type_7b
-- name    : FamousTheorems.perm_order_lcm_cycle_type_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:19.619983+00:00
-- url     : https://prove2.me/theorems/452990da-6136-4216-8d16-60322d90f097
-- title:
--   The order of a permutation is the lcm of its cycle lengths
-- statement:
--   **The order of a permutation is the lcm of its cycle lengths.** Let $\sigma$ be a permutation of a finite set, written as a product of disjoint cycles of lengths $\ell_1,\dots,\ell_r$. Then the order of $\sigma$ is $\operatorname{lcm}(\ell_1,\dots,\ell_r)$.
--
--   This is used to compute the orders of elements of symmetric groups, for instance in card shuffling, and it leads to Landau's function $g(n)$, the maximal order of an element of $S_n$. It holds because disjoint cycles commute and a cycle of length $\ell$ has order $\ell$.
--
--   **Formalization note.** Mathlib's `Equiv.Perm.lcm_cycleType`. `σ.cycleType` is the multiset of lengths of the nontrivial cycles, and `Multiset.lcm` is its least common multiple, equal to $1$ for the identity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Equiv.Perm.lcm_cycleType`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem perm_order_lcm_cycle_type_7b {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : σ.cycleType.lcm = orderOf σ := by sorry

end FamousTheorems
