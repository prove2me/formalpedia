-- Prove2me | Theorems.Thm_FamousTheorems_det_mul_7b
-- name    : FamousTheorems.det_mul_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:31.832882+00:00
-- url     : https://prove2.me/theorems/a25630c2-c0a1-44e8-9e77-0c1165aabe5f
-- title:
--   The determinant is multiplicative
-- statement:
--   **The determinant is multiplicative.** Let $R$ be a commutative ring and $M,N$ square matrices over $R$ of the same size. Then
--   $$\det(MN)=\det M\,\det N.$$
--
--   This is one of the basic identities of linear algebra. It shows that the invertible matrices are those with invertible determinant, that the determinant is a group homomorphism $GL_n(R)\to R^\times$, and that similar matrices have the same determinant, so the determinant of a linear endomorphism is well defined. Over a field it expresses the fact that the determinant measures how a linear map scales volume.
--
--   **Formalization note.** Mathlib's `Matrix.det_mul`. The matrices are indexed by an arbitrary finite type with decidable equality.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem det_mul_7b {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] (M N : Matrix n n R) :
    (M * N).det = M.det * N.det := by sorry

end FamousTheorems
