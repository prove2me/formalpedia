-- Prove2me | Theorems.Thm_FamousTheorems_fundamental_theorem_galois_theory
-- name    : FamousTheorems.fundamental_theorem_galois_theory
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:54.302463+00:00
-- url     : https://prove2.me/theorems/9f7ffa7d-4dc0-47e7-b12c-73a031afd197
-- title:
--   Fundamental theorem of Galois theory
-- statement:
--   **The fundamental theorem of Galois theory.** Let $E/F$ be a finite Galois extension with Galois group $G=\mathrm{Gal}(E/F)$. Then intermediate fields and subgroups correspond bijectively:
--   1. every intermediate field $K$ is the fixed field of its fixing subgroup: $E^{\mathrm{Gal}(E/K)}=K$;
--   2. every subgroup $H\le G$ is the fixing subgroup of its fixed field: $\mathrm{Gal}(E/E^H)=H$.
--
--   The correspondence is inclusion-reversing and translates field-theoretic questions into group theory. It is the basis of the proof of the unsolvability of the quintic by radicals and of the classification of constructible regular polygons.
--
--   **Formalization note.** Mathlib's `IsGalois.fixedField_fixingSubgroup` and `IntermediateField.fixingSubgroup_fixedField`, which Mathlib packages as the order isomorphism `IsGalois.intermediateFieldEquivSubgroup`. `K.fixingSubgroup` is the subgroup of `E ≃ₐ[F] E` fixing `K` pointwise, and `IntermediateField.fixedField H` is the subfield fixed by `H`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsGalois.fixedField_fixingSubgroup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fundamental_theorem_galois_theory {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    (∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
      ∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H := by sorry

end FamousTheorems
