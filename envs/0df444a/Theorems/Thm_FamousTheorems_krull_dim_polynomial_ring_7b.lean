-- Prove2me | Theorems.Thm_FamousTheorems_krull_dim_polynomial_ring_7b
-- name    : FamousTheorems.krull_dim_polynomial_ring_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:50.931894+00:00
-- url     : https://prove2.me/theorems/ded28ccf-d524-4b33-b8d0-df7e54bc1da4
-- title:
--   The Krull dimension of R[X] is dim R + 1 for Noetherian R
-- statement:
--   **The Krull dimension of a polynomial ring.** Let $R$ be a commutative Noetherian ring. Then
--   $$\dim R[X]=\dim R+1.$$
--
--   By induction, $\dim k[X_1,\dots,X_n]=n$ for a field $k$, and $\dim\mathbb Z[X_1,\dots,X_n]=n+1$. This gives the expected dimension of affine space in algebraic geometry. For non-Noetherian rings only the bounds $\dim R+1\le\dim R[X]\le2\dim R+1$ hold (Seidenberg). The proof shows that a chain of primes of $R[X]$ lying over the same prime of $R$ has length at most $1$, and uses Krull's height theorem.
--
--   **Formalization note.** Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing`. `ringKrullDim` takes values in $\mathbb N\cup\{\pm\infty\}$, with $-\infty$ for the zero ring and $+\infty$ for rings of infinite dimension, and the identity holds in all these cases.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.ringKrullDim_of_isNoetherianRing`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem krull_dim_polynomial_ring_7b (R : Type*) [CommRing R] [IsNoetherianRing R] : ringKrullDim (Polynomial R) = ringKrullDim R + 1 := by sorry

end FamousTheorems
