-- Prove2me | Theorems.Thm_FamousTheorems_dedekind_independence_of_characters
-- name    : FamousTheorems.dedekind_independence_of_characters
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:58.960964+00:00
-- url     : https://prove2.me/theorems/6e257b0b-0ceb-4804-9f7e-496692368c14
-- title:
--   Dedekind's lemma on independence of characters
-- statement:
--   **Dedekind's lemma on the independence of characters.** Let $G$ be a monoid and $L$ an integral domain. Then the distinct monoid homomorphisms $G\to(L,\cdot)$ are linearly independent over $L$ as functions $G\to L$.
--
--   Also known as Artin's theorem on characters, this is a basic ingredient of Galois theory. Applied to distinct field embeddings, it gives the inequality $[E:F]\ge|\mathrm{Aut}(E/F)|$ and it is used in proofs of the normal basis theorem and of Hilbert's Theorem 90.
--
--   **Formalization note.** Mathlib's `linearIndependent_monoidHom`. The family is indexed by `G →* L` itself, so linear independence of the family `fun f => ⇑f` says exactly that distinct homomorphisms are independent. `G` need only be a `MulOneClass`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `linearIndependent_monoidHom`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dedekind_independence_of_characters (G L : Type*) [MulOneClass G] [CommRing L] [IsDomain L] :
    LinearIndependent L (fun f : G →* L => (f : G → L)) := by sorry

end FamousTheorems
