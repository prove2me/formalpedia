-- Prove2me | Theorems.Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
-- name    : CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/5551b5fa-387a-52b3-9b39-b2112861b195
-- title:
--   Infinitely many degree-one primes for an order
-- statement:
--   Let $R$ be a commutative ring, assumed to be an integral domain of characteristic zero which is finite as a $\mathbb{Z}$-module, i.e. finitely generated as an abelian group (so $R$ is an order in the number field $\operatorname{Frac} R$). The assertion is that the set of natural numbers $\ell$ such that $\ell$ is prime and the type of ring homomorphisms $R \to \mathbb{Z}/\ell\mathbb{Z}$ is nonempty — that is, such that at least one ring homomorphism $R \to \mathbb{Z}/\ell\mathbb{Z}$ exists — is an infinite subset of $\mathbb{N}$. Since a ring homomorphism from $R$ onto the field $\mathbb{F}_\ell$ is the same thing as a prime of $R$ of residue degree one above $\ell$, the conclusion says that $R$ admits primes of residue degree one over infinitely many rational primes $\ell$. Note that $R$ is required to live in `Type` (rather than an arbitrary universe).
--
--   This is the statement that an order in a number field, equivalently the number field itself, has infinitely many primes of residue degree one; it is a weak qualitative form of the Chebotarev-type density statement that degree-one primes have positive density. The proof draws on an asymptotic estimate for Dirichlet series counting degree-one primes, [`FrobeniusDensity.degOneSum_add_log_isBigO`](thm.html#FrobeniusDensity.degOneSum_add_log_isBigO), and the result is used both in the existence of degree-one primes of a number field avoiding a finite set and splitting in no given extension, and in the Deligne–Serre construction of a Galois representation with prescribed Frobenius traces from a compatible family of residual representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R] :
    {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}.Infinite := by sorry
