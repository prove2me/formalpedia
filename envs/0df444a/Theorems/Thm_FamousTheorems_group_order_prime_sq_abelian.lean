-- Prove2me | Theorems.Thm_FamousTheorems_group_order_prime_sq_abelian
-- name    : FamousTheorems.group_order_prime_sq_abelian
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:15.366297+00:00
-- url     : https://prove2.me/theorems/2c94a01c-720a-4056-aab5-c184206dad55
-- title:
--   Groups of order p² are abelian
-- statement:
--   **Groups of order $p^2$ are abelian.** Let $p$ be a prime. Every group of order $p^2$ is abelian.
--
--   Since $Z(G)$ is nontrivial, $G/Z(G)$ has order $1$ or $p$ and is therefore cyclic, so $G$ is abelian. Hence a group of order $p^2$ is isomorphic to $\mathbb Z/p^2$ or $(\mathbb Z/p)^2$. The bound is sharp: for every prime $p$ there are non-abelian groups of order $p^3$.
--
--   **Formalization note.** Mathlib's `IsPGroup.isMulCommutative_of_card_eq_prime_sq`. `Nat.card G` is the order of `G`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsPGroup.isMulCommutative_of_card_eq_prime_sq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem group_order_prime_sq_abelian {p : ℕ} {G : Type*} [Group G] [Fact p.Prime] (h : Nat.card G = p ^ 2) : IsMulCommutative G := by sorry

end FamousTheorems
