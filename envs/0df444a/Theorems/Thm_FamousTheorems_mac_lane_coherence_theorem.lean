-- Prove2me | Theorems.Thm_FamousTheorems_mac_lane_coherence_theorem
-- name    : FamousTheorems.mac_lane_coherence_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:47.51715+00:00
-- url     : https://prove2.me/theorems/7691019b-abfa-4829-b1a6-aaf1de40abaa
-- title:
--   Mac Lane's coherence theorem for monoidal categories
-- statement:
--   **Mac Lane's coherence theorem for monoidal categories.** In the free monoidal category on a set $C$ of objects, any two morphisms with the same source and target are equal.
--
--   Equivalently, every diagram built from associators, unitors and their inverses commutes. This is why, in any monoidal category, one can in practice treat the tensor product as strictly associative and unital. Mac Lane proved it in 1963, and it is the prototype of coherence theorems in higher category theory.
--
--   **Formalization note.** Mathlib's `CategoryTheory.FreeMonoidalCategory.subsingleton_hom`. `FreeMonoidalCategory C` is the free monoidal category on the type `C`, and `Quiver.IsThin` says that every hom-type has at most one element.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.FreeMonoidalCategory.subsingleton_hom`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mac_lane_coherence_theorem (C : Type*) : Quiver.IsThin (CategoryTheory.FreeMonoidalCategory C) := by sorry

end FamousTheorems
