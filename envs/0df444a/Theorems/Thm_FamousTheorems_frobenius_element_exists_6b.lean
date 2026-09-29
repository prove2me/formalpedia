-- Prove2me | Theorems.Thm_FamousTheorems_frobenius_element_exists_6b
-- name    : FamousTheorems.frobenius_element_exists_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:23.08398+00:00
-- url     : https://prove2.me/theorems/b3e2bc2b-a2e8-4dac-ad4b-14b413906c42
-- title:
--   Existence of Frobenius elements
-- statement:
--   **Existence of Frobenius elements.** Let $G$ be a finite group acting on a commutative ring $S$ by ring automorphisms, and let $R\to S$ be such that $R$ is the ring of invariants $S^G$, in the sense of `Algebra.IsInvariant`. Let $Q$ be a prime ideal of $S$ with finite residue ring $S/Q$. Then there is $\sigma\in G$ that is an arithmetic Frobenius at $Q$:
--   $$\sigma(x)\equiv x^{q}\pmod Q\quad\text{for all }x\in S,$$
--   where $q=|R/(Q\cap R)|$.
--
--   Frobenius elements link Galois groups to prime ideals. They are the input to the Chebotarev density theorem, to Artin reciprocity and Artin $L$-functions, and to the definition of Galois representations attached to arithmetic objects.
--
--   **Formalization note.** Mathlib's `IsArithFrobAt.exists_of_isInvariant`. `IsArithFrobAt R σ Q` says that $\sigma(x)-x^{q}\in Q$ for all $x\in S$, where $q$ is the cardinality of $R/(Q\cap R)$. `Algebra.IsInvariant R S G` says that every $G$-fixed element of $S$ comes from $R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsArithFrobAt.exists_of_isInvariant`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem frobenius_element_exists_6b (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Group G]
    [MulSemiringAction G S] [SMulCommClass G R S] (Q : Ideal S) [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] : ∃ σ : G, IsArithFrobAt R σ Q := by sorry

end FamousTheorems
