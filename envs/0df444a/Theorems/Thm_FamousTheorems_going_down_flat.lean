-- Prove2me | Theorems.Thm_FamousTheorems_going_down_flat
-- name    : FamousTheorems.going_down_flat
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:55.846042+00:00
-- url     : https://prove2.me/theorems/220122f4-db1e-429f-bfc7-3daf8cb89387
-- title:
--   The going-down theorem for flat extensions
-- statement:
--   **The going-down theorem for flat extensions.** Let $R\to S$ be a flat homomorphism of commutative rings. Let $p\subsetneq q$ be primes of $R$ and $Q$ a prime of $S$ lying over $q$. Then there is a prime $P\subsetneq Q$ of $S$ lying over $p$.
--
--   Chains of primes descend along flat maps, which makes $\operatorname{Spec}S\to\operatorname{Spec}R$ generalising and gives $\dim S_Q\ge\dim R_q$. Going-down for flat and for integral extensions of normal domains are the two classical Cohen–Seidenberg going-down theorems. This entry is the flat case.
--
--   **Formalization note.** Mathlib's instance `Algebra.HasGoingDown.of_flat` (flat algebras satisfy going down), used through `Ideal.exists_ideal_lt_liesOver_of_lt`. `Q.LiesOver q` means `Q` contracts to `q`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Algebra.HasGoingDown.of_flat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem going_down_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] {p q : Ideal R} [p.IsPrime]
    [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] (hpq : p < q) :
    ∃ P < Q, P.IsPrime ∧ P.LiesOver p := by sorry

end FamousTheorems
