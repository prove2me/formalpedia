-- Prove2me | Theorems.Thm_FamousTheorems_prime_order_group_cyclic_7b
-- name    : FamousTheorems.prime_order_group_cyclic_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:27.986982+00:00
-- url     : https://prove2.me/theorems/2879ba88-83f7-4967-b8f1-cd2ee84ab4aa
-- title:
--   Groups of prime order are cyclic
-- statement:
--   **Groups of prime order are cyclic.** Let $G$ be a group of prime order $p$. Then $G$ is cyclic.
--
--   This is a direct consequence of Lagrange's theorem: any element $g\neq1$ generates a subgroup whose order divides $p$ and is greater than $1$, so it is all of $G$. It follows that there is only one group of each prime order up to isomorphism, namely $\mathbb Z/p\mathbb Z$, and that such groups are simple and abelian.
--
--   **Formalization note.** Mathlib's `isCyclic_of_prime_card`. `Nat.card G` is the cardinality of $G$, which is $0$ if $G$ is infinite, so the hypothesis forces $G$ to be finite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isCyclic_of_prime_card`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prime_order_group_cyclic_7b {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] (h : Nat.card G = p) : IsCyclic G := by sorry

end FamousTheorems
