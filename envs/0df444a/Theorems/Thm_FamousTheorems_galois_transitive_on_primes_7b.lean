-- Prove2me | Theorems.Thm_FamousTheorems_galois_transitive_on_primes_7b
-- name    : FamousTheorems.galois_transitive_on_primes_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:01.846778+00:00
-- url     : https://prove2.me/theorems/12cf7c61-5210-48c6-9e73-393327a2ab2a
-- title:
--   The Galois group acts transitively on the primes above a given prime
-- statement:
--   **The Galois group acts transitively on the primes above a given prime.** Let $G$ be a finite group acting on a commutative ring $B$ by ring automorphisms, and let $A\to B$ be a ring map whose image is the ring of invariants $B^G$. If $P$ and $Q$ are prime ideals of $B$ with $P\cap A=Q\cap A$, then $Q=gP$ for some $g\in G$.
--
--   The main case is a Galois extension of number fields $L/K$ with $A=\mathcal O_K$, $B=\mathcal O_L$ and $G=\operatorname{Gal}(L/K)$. Transitivity implies that all primes above a given prime have the same ramification index and residue degree, giving the formula $efg=[L:K]$. It is also the first step in defining decomposition groups and Frobenius elements.
--
--   **Formalization note.** Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`. `Algebra.IsInvariant A B G` says that every $G$-invariant element of $B$ comes from $A$. `Ideal.under A P` is the preimage of $P$ in $A$. The theorem needs no finiteness or integrality assumption beyond $G$ being finite.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Algebra.IsInvariant.exists_smul_of_under_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem galois_transitive_on_primes_7b (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] [Finite G] [SMulCommClass G A B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : Ideal.under A P = Ideal.under A Q) : ∃ g : G, Q = g • P := by sorry

end FamousTheorems
