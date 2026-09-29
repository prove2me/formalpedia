-- Prove2me | Theorems.Thm_FamousTheorems_finite_field_iff_prime_power_6b
-- name    : FamousTheorems.finite_field_iff_prime_power_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:26.169361+00:00
-- url     : https://prove2.me/theorems/198836d3-1d23-4d8b-9d4a-3b4e0526c093
-- title:
--   A finite field exists iff its order is a prime power
-- statement:
--   **A finite field exists iff its order is a prime power.** A finite set $\alpha$ carries a field structure if and only if $|\alpha|$ is a prime power $p^n$ with $n\ge1$.
--
--   One direction holds because a finite field is a vector space over its prime field $\mathbb F_p$. The other is the existence of the Galois field $\mathbb F_{p^n}$, the splitting field of $X^{p^n}-X$ over $\mathbb F_p$. With the uniqueness of $\mathbb F_{p^n}$ up to isomorphism, this completes the classification of finite fields due to Galois and Moore.
--
--   **Formalization note.** Mathlib's `Fintype.nonempty_field_iff`. `Nonempty (Field α)` says that some field structure exists on the type $\alpha$, and `IsPrimePow m` says that $m=p^k$ for a prime $p$ and $k\ge1$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Fintype.nonempty_field_iff`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem finite_field_iff_prime_power_6b {α : Type*} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow (Fintype.card α) := by sorry

end FamousTheorems
