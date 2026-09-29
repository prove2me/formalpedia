-- Prove2me | Theorems.Thm_FamousTheorems_sylvester_determinant
-- name    : FamousTheorems.sylvester_determinant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:26.072533+00:00
-- url     : https://prove2.me/theorems/9586b77a-c2f2-4ba8-a168-66fce71b181c
-- title:
--   Sylvester's determinant theorem
-- statement:
--   **Sylvester's determinant theorem.** For an $m\times n$ matrix $A$ and an $n\times m$ matrix $B$ over a commutative ring,
--   $$\det(I_m+AB)=\det(I_n+BA).$$
--
--   A large determinant can be computed as a small one, e.g. $\det(I+uv^{\mathsf T})=1+v^{\mathsf T}u$ (the matrix determinant lemma). It is used in random matrix theory, Fredholm determinants and the analysis of low-rank perturbations.
--
--   **Formalization note.** Mathlib's `Matrix.det_one_add_mul_comm`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_one_add_mul_comm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sylvester_determinant {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α] (A : Matrix m n α)
    (B : Matrix n m α) : (1 + A * B).det = (1 + B * A).det := by sorry

end FamousTheorems
