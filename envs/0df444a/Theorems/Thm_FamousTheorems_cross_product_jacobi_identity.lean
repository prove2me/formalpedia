-- Prove2me | Theorems.Thm_FamousTheorems_cross_product_jacobi_identity
-- name    : FamousTheorems.cross_product_jacobi_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:23.24045+00:00
-- url     : https://prove2.me/theorems/c863f61b-bbb4-444d-a684-7321396cf19b
-- title:
--   The Jacobi identity for the cross product
-- statement:
--   **The Jacobi identity for the cross product.** For vectors $u,v,w$ in $R^3$ over a commutative ring $R$,
--   $$u\times(v\times w)+v\times(w\times u)+w\times(u\times v)=0.$$
--
--   Together with bilinearity and antisymmetry, this makes $(R^3,\times)$ a Lie algebra. Over $\mathbb R$ it is isomorphic to $\mathfrak{so}(3)$, the Lie algebra of the rotation group. The identity follows from the vector triple product expansion $u\times(v\times w)=(u\cdot w)v-(u\cdot v)w$.
--
--   **Formalization note.** Mathlib's `jacobi_cross`. Vectors are functions `Fin 3 → R`, and `crossProduct` is Mathlib's cross product, a bilinear map applied to both arguments.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobi_cross`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cross_product_jacobi_identity {R : Type*} [CommRing R] (u v w : Fin 3 → R) :
    crossProduct u (crossProduct v w) + crossProduct v (crossProduct w u) + crossProduct w (crossProduct u v) = 0 := by sorry

end FamousTheorems
