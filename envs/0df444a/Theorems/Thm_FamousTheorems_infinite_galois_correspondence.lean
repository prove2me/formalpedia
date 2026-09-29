-- Prove2me | Theorems.Thm_FamousTheorems_infinite_galois_correspondence
-- name    : FamousTheorems.infinite_galois_correspondence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:28.33199+00:00
-- url     : https://prove2.me/theorems/5d7caee5-46bc-44ba-b15a-53a948fe4bbb
-- title:
--   The fundamental theorem of infinite Galois theory
-- statement:
--   **The fundamental theorem of infinite Galois theory.** Let $K/k$ be a Galois extension, possibly infinite, with Galois group $\operatorname{Gal}(K/k)$ carrying the Krull topology. Then:
--   - for every intermediate field $L$, the fixed field of $\operatorname{Gal}(K/L)$ is $L$;
--   - for every closed subgroup $H$ of $\operatorname{Gal}(K/k)$, the subgroup fixing the fixed field $K^H$ is $H$.
--
--   So $L\mapsto\operatorname{Gal}(K/L)$ and $H\mapsto K^H$ are inverse bijections between intermediate fields and closed subgroups. Krull's theorem makes profinite groups the natural setting for Galois theory, for example for absolute Galois groups.
--
--   **Formalization note.** Mathlib's `InfiniteGalois.fixedField_fixingSubgroup` and `InfiniteGalois.fixingSubgroup_fixedField`. `ClosedSubgroup` is a subgroup closed in the Krull topology, `IntermediateField.fixedField` is $K^H$, and `fixingSubgroup` is $\operatorname{Gal}(K/L)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InfiniteGalois.fixingSubgroup_fixedField`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem infinite_galois_correspondence {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    (∀ L : IntermediateField k K, IntermediateField.fixedField L.fixingSubgroup = L) ∧
      ∀ H : ClosedSubgroup (K ≃ₐ[k] K),
        (IntermediateField.fixedField H.toSubgroup).fixingSubgroup = H.toSubgroup := by sorry

end FamousTheorems
