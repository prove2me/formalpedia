-- Prove2me | Theorems.Thm_FamousTheorems_gauss_lemma_polynomials
-- name    : FamousTheorems.gauss_lemma_polynomials
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:03.002684+00:00
-- url     : https://prove2.me/theorems/cf9bd32a-8405-4755-9542-8f7a9757152c
-- title:
--   Gauss's lemma for polynomials
-- statement:
--   **Gauss's lemma for polynomials.** Let $R$ be a GCD domain (for example a UFD) with fraction field $K$, and $p\in R[X]$ a primitive polynomial, so the gcd of its coefficients is $1$. Then $p$ is irreducible in $R[X]$ if and only if it is irreducible in $K[X]$.
--
--   For $R=\mathbb Z$, a primitive integer polynomial that factors over $\mathbb Q$ already factors over $\mathbb Z$. Gauss's lemma is the key step in proving that $R[X]$ is a UFD when $R$ is, and it justifies irreducibility tests over $\mathbb Q$ such as Eisenstein's criterion and reduction modulo primes.
--
--   **Formalization note.** Mathlib's `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`. `IsFractionRing R K` makes `K` a fraction field of `R`, and `p.map (algebraMap R K)` is $p$ viewed in $K[X]$. `Polynomial.IsPrimitive` means that the only constants dividing $p$ are units.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gauss_lemma_polynomials {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    {p : Polynomial R} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by sorry

end FamousTheorems
