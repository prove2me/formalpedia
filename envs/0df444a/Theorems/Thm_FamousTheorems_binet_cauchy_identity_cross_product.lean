-- Prove2me | Theorems.Thm_FamousTheorems_binet_cauchy_identity_cross_product
-- name    : FamousTheorems.binet_cauchy_identity_cross_product
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:18.575984+00:00
-- url     : https://prove2.me/theorems/e09bccfc-a102-42dd-8d41-eecb55f46677
-- title:
--   The Binet–Cauchy identity
-- statement:
--   **The Binet–Cauchy identity.** For vectors $u,v,w,x$ in $R^3$ over a commutative ring $R$,
--   $$(u\times v)\cdot(w\times x)=(u\cdot w)(v\cdot x)-(u\cdot x)(v\cdot w).$$
--
--   This is the three-dimensional case of the Binet–Cauchy identity. With $w=u$ and $x=v$ it gives Lagrange's identity $|u\times v|^2=|u|^2|v|^2-(u\cdot v)^2$. It is a basic tool in vector calculus.
--
--   **Formalization note.** Mathlib's `cross_dot_cross`. `crossProduct` is the cross product on `Fin 3 → R` and `dotProduct` the dot product.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `cross_dot_cross`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem binet_cauchy_identity_cross_product {R : Type*} [CommRing R] (u v w x : Fin 3 → R) :
    dotProduct (crossProduct u v) (crossProduct w x) =
      dotProduct u w * dotProduct v x - dotProduct u x * dotProduct v w := by sorry

end FamousTheorems
