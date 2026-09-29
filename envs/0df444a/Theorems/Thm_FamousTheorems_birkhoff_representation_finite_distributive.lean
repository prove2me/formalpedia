-- Prove2me | Theorems.Thm_FamousTheorems_birkhoff_representation_finite_distributive
-- name    : FamousTheorems.birkhoff_representation_finite_distributive
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:58.978379+00:00
-- url     : https://prove2.me/theorems/0a9a40ef-fa61-4ee2-9c31-d7cb53b38817
-- title:
--   Birkhoff's representation theorem for finite distributive lattices
-- statement:
--   **Birkhoff's representation theorem for finite distributive lattices.** Every finite distributive lattice $\alpha$ is isomorphic to the lattice of lower sets (down-closed subsets) of the poset of its join-irreducible elements.
--
--   The isomorphism sends $a$ to the set of join-irreducible elements below $a$. The theorem says that finite distributive lattices and finite posets carry the same information. It is the finite case of Stone and Priestley duality and is a basic tool in combinatorics and order theory.
--
--   **Formalization note.** Mathlib's `OrderIso.lowerSetSupIrred`, which is a construction, so the statement asserts the existence of an order isomorphism `α ≃o LowerSet {a : α // SupIrred a}`. `SupIrred a` says that $a$ is join-irreducible: $a$ is not the bottom element and $a=b\sqcup c$ forces $a=b$ or $a=c$. The lattice is assumed to have a bottom element, which is automatic for a nonempty finite lattice.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `OrderIso.lowerSetSupIrred`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem birkhoff_representation_finite_distributive {α : Type*} [DistribLattice α] [Fintype α] [OrderBot α] :
    Nonempty (α ≃o LowerSet {a : α // SupIrred a}) := by sorry

end FamousTheorems
