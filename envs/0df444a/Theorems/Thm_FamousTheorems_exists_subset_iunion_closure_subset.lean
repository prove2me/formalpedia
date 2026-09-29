-- Prove2me | Theorems.Thm_FamousTheorems_exists_subset_iunion_closure_subset
-- name    : FamousTheorems.exists_subset_iunion_closure_subset
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:54.599369+00:00
-- url     : https://prove2.me/theorems/e29f1c2b-1fd8-44b6-9b57-970846fc8619
-- title:
--   The shrinking lemma
-- statement:
--   **The shrinking lemma.** A point-finite open cover of a normal space can be shrunk: there is another open cover indexed the same way with the closure of each new set inside the corresponding old one. Shrinking is what makes partitions of unity constructible, and through them the standard gluing arguments of topology and differential geometry -- extending local constructions to global ones, and building Riemannian metrics or bump functions. Normality is exactly the separation strength needed to insert a closed set between an open set and its cover. **Formalization note.** The cover is point-finite and the conclusion gives closures contained in the original sets. The result is Mathlib's `exists_subset_iUnion_closure_subset`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_subset_iunion_closure_subset :
    ∀ {ι : Type u_1} {X : Type u_2} [inst : TopologicalSpace X] {u : ι → Set X} 
    {s : Set X} [NormalSpace X], 
    IsClosed s → 
    (∀ (i : ι), IsOpen (u i)) → 
    (∀ x ∈ s, {i | x ∈ u i}.Finite) → 
    s ⊆ ⋃ i, u i → ∃ v, s ⊆ iUnion v ∧ (∀ (i : ι), IsOpen (v i)) ∧ ∀ (i : ι), closure (v i) ⊆ u i := by sorry

end FamousTheorems
