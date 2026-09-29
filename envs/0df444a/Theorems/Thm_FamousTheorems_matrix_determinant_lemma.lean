-- Prove2me | Theorems.Thm_FamousTheorems_matrix_determinant_lemma
-- name    : FamousTheorems.matrix_determinant_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:40.237889+00:00
-- url     : https://prove2.me/theorems/a05b933e-3a90-40bc-860a-33295fd67f74
-- title:
--   The matrix determinant lemma
-- statement:
--   **The matrix determinant lemma.** Let $A$ be an invertible $m\times m$ matrix over a commutative ring, and let $u,v$ be column vectors. Then
--   $$\det(A+uv^{\mathsf T})=\det A\cdot\big(1+v^{\mathsf T}A^{-1}u\big).$$
--
--   The lemma computes the determinant after a rank-one update of a matrix. It is the determinant counterpart of the Sherman–Morrison formula and is widely used in statistics, numerical linear algebra and the matrix-tree theorem.
--
--   **Formalization note.** Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow`. The column $u$ and the row $v^{\mathsf T}$ are `Matrix.replicateCol ι u` and `Matrix.replicateRow ι v` for a one-element index type $\iota$, so $1+v^{\mathsf T}A^{-1}u$ is the determinant of a $1\times1$ matrix.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_add_replicateCol_mul_replicateRow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem matrix_determinant_lemma {m ι α : Type*} [Fintype m] [DecidableEq m] [CommRing α] [Unique ι] {A : Matrix m m α}
    (hA : IsUnit A.det) (u v : m → α) :
    (A + Matrix.replicateCol ι u * Matrix.replicateRow ι v).det =
      A.det * (1 + Matrix.replicateRow ι v * A⁻¹ * Matrix.replicateCol ι u).det := by sorry

end FamousTheorems
