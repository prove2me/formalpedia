-- Prove2me | Theorems.Thm_FamousTheorems_prime_ideal_theorem_distributive_lattice
-- name    : FamousTheorems.prime_ideal_theorem_distributive_lattice
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:58.063126+00:00
-- url     : https://prove2.me/theorems/e66829c8-d975-4edd-945c-5f5dd936e31b
-- title:
--   The prime ideal theorem for distributive lattices
-- statement:
--   **The prime ideal theorem for distributive lattices.** Let $F$ be a filter and $I$ an ideal in a distributive lattice, with $F\cap I=\varnothing$. Then there is a prime ideal $J\supseteq I$ that is still disjoint from $F$.
--
--   This separation theorem, due to Stone, is the key step in Stone's representation theorem: every distributive lattice embeds into a lattice of sets. It is a weak form of the axiom of choice, equivalent to the Boolean prime ideal theorem.
--
--   **Formalization note.** Mathlib's `DistribLattice.prime_ideal_of_disjoint_filter_ideal`. `Order.PFilter α` is a (proper or improper) filter, `Order.Ideal α` is an order ideal, and `J.IsPrime` means $J$ is a proper ideal whose complement is a filter. Disjointness is stated for the underlying sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `DistribLattice.prime_ideal_of_disjoint_filter_ideal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prime_ideal_theorem_distributive_lattice {α : Type*} [DistribLattice α] {F : Order.PFilter α} {I : Order.Ideal α}
    (h : Disjoint (F : Set α) (I : Set α)) :
    ∃ J : Order.Ideal α, J.IsPrime ∧ I ≤ J ∧ Disjoint (F : Set α) (J : Set α) := by sorry

end FamousTheorems
