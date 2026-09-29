-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
-- name    : AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2f4e6854-72f9-5839-801b-66eac2ee3781
-- title:
--   Symmetric Hochschild 2-cocycles are coboundaries up to a multiplier
-- statement:
--   Let $K$ be a field, $n$ a natural number, and $B$ a commutative integrally closed domain which is an algebra over the polynomial ring $K[X]$, equipped with a $K[X]$-basis $b_0,\dots,b_n$ indexed by $\mathrm{Fin}\,(n+1)$ such that $b_0=1$ and such that the discriminant $\operatorname{discr}_{K[X]}(b)$ is nonzero. Write $\gamma_{ijk}=\,$`b.repr (b i * b j) k` for the structure constants, i.e. the $b_k$-coordinate of $b_ib_j$ in this basis. Let $\psi_{ijk}\in K[X]$ be a family of polynomials indexed by three elements of $\mathrm{Fin}\,(n+1)$ satisfying: normalisation $\psi_{0jk}=0$ for all $j,k$; symmetry $\psi_{ijk}=\psi_{jik}$ for all $i,j,k$; and the cocycle identity $$\sum_k\psi_{jlk}\gamma_{ikm}-\sum_k\gamma_{ijk}\psi_{klm}+\sum_k\gamma_{jlk}\psi_{ikm}-\sum_k\psi_{ijk}\gamma_{klm}=0$$ for all $i,j,l,m$. Then there exist a nonzero $u\in K[X]$ and a family $\lambda_{im}\in K[X]$ with $\lambda_{0m}=0$ for all $m$, such that for all $i,j,m$ $$u\,\psi_{ijm}=\sum_k\lambda_{jk}\gamma_{ikm}-\sum_k\gamma_{ijk}\lambda_{km}+\sum_k\lambda_{ik}\gamma_{kjm}.$$ Thus $u\psi$ is the Hochschild coboundary of a normalised $1$-cochain $\lambda$, with coefficients in $K[X]$.
--
--   This is the statement that, for a finite cover with nonzero discriminant, a normalised symmetric Hochschild $2$-cocycle written in terms of the structure constants of a basis becomes a coboundary after multiplication by a single nonzero polynomial; the multiplier absorbs the denominators introduced by passing to the generically separable situation over $K(X)$, where the cocycle splits by formal smoothness ([`Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle`](thm.html#Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle)). It is used in the construction of lifts of structure constants in normal form across a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u v

theorem AlgebraicCurve.exists_mul_eq_hochschild_coboundary_of_discr_ne_zero
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, (∑ k, ψ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * ψ k l m) +
        (∑ k, b.repr (b j * b l) k * ψ i k m) - (∑ k, ψ i j k * b.repr (b k * b l) m) = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = (∑ k, lam j k * b.repr (b i * b k) m) -
        (∑ k, b.repr (b i * b j) k * lam k m) + (∑ k, lam i k * b.repr (b k * b j) m) := by sorry
