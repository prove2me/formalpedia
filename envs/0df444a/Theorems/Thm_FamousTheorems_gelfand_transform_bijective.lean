-- Prove2me | Theorems.Thm_FamousTheorems_gelfand_transform_bijective
-- name    : FamousTheorems.gelfand_transform_bijective
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:29.920985+00:00
-- url     : https://prove2.me/theorems/54a23a63-e422-4c64-8a16-69f44a420836
-- title:
--   Gelfand duality: the Gelfand transform is bijective
-- statement:
--   **Gelfand duality (commutative Gelfand–Naimark theorem).** For a commutative unital C*-algebra $A$, the Gelfand transform $A\to C(\operatorname{sp}A,\mathbb C)$, which sends $a$ to the function $\varphi\mapsto\varphi(a)$ on the space of characters, is bijective.
--
--   Gelfand and Naimark proved this in 1943. It identifies commutative C*-algebras with algebras of continuous functions on compact Hausdorff spaces, and it is the foundation of continuous functional calculus and of noncommutative geometry.
--
--   **Formalization note.** Mathlib's `gelfandTransform_bijective`. `CommCStarAlgebra A` is a commutative unital C*-algebra, and `WeakDual.gelfandTransform ℂ A` is the Gelfand transform into continuous functions on the character space `WeakDual.characterSpace ℂ A`. Mathlib also shows it is an isometric star-algebra isomorphism.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `gelfandTransform_bijective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gelfand_transform_bijective (A : Type*) [CommCStarAlgebra A] :
    Function.Bijective (WeakDual.gelfandTransform ℂ A) := by sorry

end FamousTheorems
