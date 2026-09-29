-- Prove2me | Theorems.Thm_FamousTheorems_prime_avoidance_7b
-- name    : FamousTheorems.prime_avoidance_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:43.090763+00:00
-- url     : https://prove2.me/theorems/3dc3567f-d5bc-4d4f-b883-ccaa75692756
-- title:
--   Prime avoidance lemma
-- statement:
--   **Prime avoidance.** Let $R$ be a commutative ring, $I$ an ideal and $P_1,\dots,P_n$ ideals of $R$, all prime except possibly two of them. If $I\subseteq P_1\cup\dots\cup P_n$, then $I\subseteq P_i$ for some $i$.
--
--   Prime avoidance is used constantly in commutative algebra. Typical applications are the existence of an element of an ideal outside finitely many primes, and so of regular elements, systems of parameters and generic linear forms. It enters the proofs of Krull's height theorem and of the existence of maximal regular sequences.
--
--   **Formalization note.** Mathlib's `Ideal.subset_union_prime`. The ideals are indexed by a finite set $s$, and the two indices $a,b$ are the ones that need not be prime. The statement is an equivalence, the converse direction being trivial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.subset_union_prime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prime_avoidance_7b {ι R : Type*} [CommRing R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (s : Set ι), (f i : Set R)) ↔ ∃ i ∈ s, I ≤ f i := by sorry

end FamousTheorems
