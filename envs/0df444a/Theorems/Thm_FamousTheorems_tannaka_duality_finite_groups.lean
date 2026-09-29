-- Prove2me | Theorems.Thm_FamousTheorems_tannaka_duality_finite_groups
-- name    : FamousTheorems.tannaka_duality_finite_groups
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:57.761982+00:00
-- url     : https://prove2.me/theorems/771dd40d-64a5-465a-ba2c-9b2796cf76c2
-- title:
--   Tannaka duality for finite groups
-- statement:
--   **Tannaka duality for finite groups.** Let $G$ be a finite group and $k$ an integral domain. The canonical homomorphism from $G$ to the group of monoidal natural automorphisms of the forgetful functor on finite-dimensional representations of $G$ over $k$, which sends $g$ to the family of maps $(\rho_V(g))_V$, is bijective.
--
--   A group can therefore be reconstructed from its category of representations together with the forgetful functor. This is the simplest case of Tannaka–Krein duality, which underlies the theory of Tannakian categories and motivic Galois groups.
--
--   **Formalization note.** Mathlib's `TannakaDuality.FiniteGroup.equiv`, built from `equivHom_injective` and `equivHom_surjective`. `TannakaDuality.FiniteGroup.equivHom k G : G →* Aut (forget k G)` is the canonical map, where `forget k G` is the monoidal forgetful functor from `FDRep k G`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `TannakaDuality.FiniteGroup.equiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem tannaka_duality_finite_groups (k G : Type u) [CommRing k] [IsDomain k] [Group G] [Finite G] :
    Function.Bijective (TannakaDuality.FiniteGroup.equivHom k G) := by sorry

end FamousTheorems
