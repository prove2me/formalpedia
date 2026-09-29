-- Prove2me | Theorems.Thm_FamousTheorems_injective_star_hom_isometry_6b
-- name    : FamousTheorems.injective_star_hom_isometry_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:14.542112+00:00
-- url     : https://prove2.me/theorems/5e7b9959-977d-4932-89a5-dc2894032bd3
-- title:
--   Injective *-homomorphisms of C*-algebras are isometric
-- statement:
--   **Injective \*-homomorphisms of C\*-algebras are isometric.** Let $A$ and $B$ be (possibly non-unital) C\*-algebras and $\varphi:A\to B$ an injective \*-homomorphism. Then $\|\varphi(a)\|=\|a\|$ for every $a\in A$.
--
--   No continuity assumption is needed: the algebraic structure of a C\*-algebra determines its norm. It follows that a C\*-algebra has only one C\*-norm and that the image of a \*-homomorphism is closed. The proof reduces to self-adjoint elements, where the norm is the spectral radius, and uses the continuous functional calculus.
--
--   **Formalization note.** Mathlib's `NonUnitalStarAlgHom.isometry`. `A →⋆ₙₐ[ℂ] B` is the type of non-unital $\mathbb C$-algebra homomorphisms that commute with the star operation.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NonUnitalStarAlgHom.isometry`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem injective_star_hom_isometry_6b {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : Function.Injective φ) : Isometry φ := by sorry

end FamousTheorems
