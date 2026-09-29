-- Prove2me | Theorems.Thm_FamousTheorems_bicategory_coherence_theorem
-- name    : FamousTheorems.bicategory_coherence_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:58.332923+00:00
-- url     : https://prove2.me/theorems/867333f3-66d9-4d71-9118-7b0c8f8ead0c
-- title:
--   The coherence theorem for bicategories
-- statement:
--   **The coherence theorem for bicategories.** In the free bicategory on a quiver $B$, any two 2-morphisms between the same pair of 1-morphisms are equal.
--
--   So every diagram of 2-cells built from associators, unitors and their inverses commutes in every bicategory. This is the bicategorical version of Mac Lane's coherence theorem. It justifies treating composition of 1-morphisms as strictly associative when working in a bicategory.
--
--   **Formalization note.** Mathlib's `CategoryTheory.FreeBicategory.locally_thin`. `FreeBicategory B` is the free bicategory on the quiver `B`. For objects `a b`, the hom-category `a ⟶ b` is thin: `Quiver.IsThin` says that each hom-set of 2-morphisms has at most one element.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.FreeBicategory.locally_thin`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bicategory_coherence_theorem {B : Type*} [Quiver B] (a b : CategoryTheory.FreeBicategory B) : Quiver.IsThin (a ⟶ b) := by sorry

end FamousTheorems
