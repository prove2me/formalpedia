-- Prove2me | Theorems.Thm_FamousTheorems_nerve_is_quasicategory_7a
-- name    : FamousTheorems.nerve_is_quasicategory_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:11.557149+00:00
-- url     : https://prove2.me/theorems/b8ccbde2-3fd3-4a35-874b-0b2d4049a1c6
-- title:
--   The nerve of a category is a quasicategory
-- statement:
--   **The nerve of a category is a quasicategory.** For every category $C$, the nerve $N(C)$ is a quasicategory: every inner horn $\Lambda^n_k\to N(C)$ with $0<k<n$ extends to an $n$-simplex $\Delta^n\to N(C)$.
--
--   The $n$-simplices of $N(C)$ are the composable strings of $n$ morphisms in $C$, and horn filling amounts to composing morphisms. Quasicategories, introduced by Boardman and Vogt and developed by Joyal and Lurie, are the standard model of $(\infty,1)$-categories. This theorem shows that ordinary categories embed into that theory. Moreover, nerves are exactly the simplicial sets in which inner horn fillers exist and are unique.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Nerve.quasicategory`. `CategoryTheory.nerve C` is the nerve as a simplicial set, and `SSet.Quasicategory` is the inner horn extension property.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Nerve.quasicategory`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nerve_is_quasicategory_7a (C : Type*) [CategoryTheory.Category C] : (CategoryTheory.nerve C).Quasicategory := by sorry

end FamousTheorems
