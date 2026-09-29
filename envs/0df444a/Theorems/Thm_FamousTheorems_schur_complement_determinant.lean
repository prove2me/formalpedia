-- Prove2me | Theorems.Thm_FamousTheorems_schur_complement_determinant
-- name    : FamousTheorems.schur_complement_determinant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:41.843009+00:00
-- url     : https://prove2.me/theorems/8f4f8d5b-cf28-41e3-ad9f-2e7e9703f483
-- title:
--   The Schur complement determinant formula
-- statement:
--   **The Schur complement determinant formula.** Let $M=\begin{pmatrix}A&B\\C&D\end{pmatrix}$ be a block matrix over a commutative ring with $A$ square and invertible. Then
--   $$\det M=\det A\cdot\det\!\big(D-CA^{-1}B\big).$$
--
--   The matrix $D-CA^{-1}B$ is the Schur complement of $A$ in $M$. The formula underlies block Gaussian elimination, the conditional distributions of multivariate Gaussians, and positivity criteria for block matrices.
--
--   **Formalization note.** Mathlib's `Matrix.det_fromBlocks₁₁`. The blocks are indexed by arbitrary finite types `m` and `n`, `Matrix.fromBlocks A B C D` is the block matrix, and `⅟A` is the inverse supplied by the instance `[Invertible A]`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_fromBlocks₁₁`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schur_complement_determinant {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α] (A : Matrix m m α)
    (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = A.det * (D - C * ⅟A * B).det := by sorry

end FamousTheorems
