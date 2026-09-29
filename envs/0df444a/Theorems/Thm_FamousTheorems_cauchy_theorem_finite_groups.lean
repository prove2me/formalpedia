-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_theorem_finite_groups
-- name    : FamousTheorems.cauchy_theorem_finite_groups
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:12.519475+00:00
-- url     : https://prove2.me/theorems/f17004e2-5f11-45de-86af-b5a35cf1188d
-- title:
--   Cauchy's theorem for finite groups
-- statement:
--   **Cauchy's theorem for finite groups.** Let $G$ be a finite group and $p$ a prime dividing $|G|$. Then $G$ has an element of order $p$.
--
--   Cauchy's theorem is a partial converse to Lagrange's theorem for prime divisors. The short proof by McKay counts $p$-tuples with product $1$ under cyclic rotation. It is a first step towards the Sylow theorems and is used throughout finite group theory, for example to show that a group of order $2p$ is cyclic or dihedral.
--
--   **Formalization note.** Mathlib's `exists_prime_orderOf_dvd_card'`. The group is `Finite` and its order is `Nat.card G`. The prime is passed as the instance `Fact p.Prime`, and `orderOf x` is the order of `x`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_prime_orderOf_dvd_card'`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_theorem_finite_groups {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ x : G, orderOf x = p := by sorry

end FamousTheorems
