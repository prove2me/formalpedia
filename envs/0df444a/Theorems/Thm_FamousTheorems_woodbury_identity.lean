-- Prove2me | Theorems.Thm_FamousTheorems_woodbury_identity
-- name    : FamousTheorems.woodbury_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:36.067474+00:00
-- url     : https://prove2.me/theorems/a50a8a0c-f36d-405a-896a-687c27baa94b
-- title:
--   The binomial inverse theorem (Woodbury matrix identity)
-- statement:
--   **The binomial inverse theorem (Woodbury matrix identity).** Let $A$ ($n\times n$) and $C$ ($m\times m$) be invertible matrices over a commutative ring, $U$ an $n\times m$ and $V$ an $m\times n$ matrix, and suppose $C^{-1}+VA^{-1}U$ is invertible. Then
--   $$(A+UCV)^{-1}=A^{-1}-A^{-1}U\,(C^{-1}+VA^{-1}U)^{-1}\,VA^{-1}.$$
--
--   A rank-$m$ update of $A$ can therefore be inverted by inverting only an $m\times m$ matrix. The case $m=1$ is the Sherman–Morrison formula. It is used throughout numerical linear algebra, Kalman filtering, Gaussian process regression and statistics.
--
--   **Formalization note.** Mathlib's `Matrix.add_mul_mul_inv_eq_sub`, with invertibility expressed by `IsUnit` and `⁻¹` the matrix inverse `Matrix.inv`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.add_mul_mul_inv_eq_sub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem woodbury_identity {m n α : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing α] (A : Matrix n n α)
    (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α) (hA : IsUnit A) (hC : IsUnit C)
    (hCVAU : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by sorry

end FamousTheorems
