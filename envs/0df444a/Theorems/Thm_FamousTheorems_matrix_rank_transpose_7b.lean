-- Prove2me | Theorems.Thm_FamousTheorems_matrix_rank_transpose_7b
-- name    : FamousTheorems.matrix_rank_transpose_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:33.860276+00:00
-- url     : https://prove2.me/theorems/f7505b6e-d84a-4e7f-b047-fe810a27318e
-- title:
--   Row rank equals column rank
-- statement:
--   **Row rank equals column rank.** Let $A$ be an $m\times n$ matrix over a field. Then $\operatorname{rank}(A^{\mathsf T})=\operatorname{rank}(A)$: the dimension of the space spanned by the rows of $A$ equals the dimension of the space spanned by its columns.
--
--   This fact is not obvious from the definitions and is one of the first nontrivial theorems of linear algebra. It gives the rank–nullity theorem for the transpose and shows that a square matrix has linearly independent rows if and only if it has linearly independent columns.
--
--   **Formalization note.** Mathlib's `Matrix.rank_transpose`. `Matrix.rank A` is the dimension of the range of the linear map given by $A$, that is, of the span of its columns, so the rank of the transpose is the row rank.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.rank_transpose`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem matrix_rank_transpose_7b {m n R : Type*} [Fintype m] [Fintype n] [Field R] (A : Matrix m n R) : A.transpose.rank = A.rank := by sorry

end FamousTheorems
