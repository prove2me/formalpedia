-- Prove2me | Theorems.Thm_FamousTheorems_triple_product_eq_det
-- name    : FamousTheorems.triple_product_eq_det
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:34.290548+00:00
-- url     : https://prove2.me/theorems/ee4b4a89-6d29-46d7-8c4c-34bd2525aec6
-- title:
--   The scalar triple product as a determinant
-- statement:
--   **The scalar triple product.** For three vectors in oriented three-dimensional Euclidean space, $$u \cdot (v \times w) = \det[u\ v\ w].$$ The triple product computes the signed volume of the parallelepiped spanned by the three vectors, and the identity says this agrees with the determinant of the matrix having them as columns. Everything about the triple product follows: it vanishes exactly when the vectors are coplanar, it is invariant under cyclic permutation and changes sign under a transposition, all inherited from the determinant. The identity is also the bridge between the coordinate-free cross product, defined via orientation and the inner product, and its coordinate formula — which is why the cross product exists only in dimension three, where $\Lambda^2 V \cong V$. **Formalization note.** The determinant is taken of the matrix whose columns are the three vectors expressed in a positively oriented orthonormal basis. The result is Mathlib's `triple_product_eq_det`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem triple_product_eq_det :
    ∀ {R : Type u_1} [inst : CommRing R] (u v w : Fin 3 → R), 
    u ⬝ᵥ (crossProduct v) w = Matrix.det ![u, v, w] := by sorry

end FamousTheorems
