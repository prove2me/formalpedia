-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero
-- name    : AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a84b1751-38b3-5025-861b-59a864a3ea24
-- title:
--   Flat descent of a characteristic-zero domain to ℤ[1/n]
-- statement:
--   Let $\mathcal{O}$ be a commutative ring (in the lowest universe) which is an integral domain of characteristic $0$, and let $n$ be a natural number whose image in $\mathcal{O}$ is a unit. Then there exist a type $B_0$, a commutative ring structure on it making $B_0$ a Dedekind domain, and a ring homomorphism $i : B_0 \to \mathcal{O}$, such that the induced morphism of schemes $\operatorname{Spec} \mathcal{O} \to \operatorname{Spec} B_0$, namely `Spec.map` applied to $i$ viewed as a morphism of `CommRingCat`, is flat in the sense of the scheme-theoretic property `AlgebraicGeometry.Flat`, and the image of $n$ in $B_0$ is a unit. Thus a characteristic-zero domain in which $n$ is invertible admits a flat structure morphism over a Dedekind base in which $n$ is likewise invertible; no finiteness or finite-type condition on $i$ is asserted.
--
--   This is the descent-of-base step used to replace an arbitrary characteristic-zero coefficient domain by the arithmetic base $\mathbb{Z}[1/n]$, over which the usual structure theory of Dedekind domains is available. It is invoked in the verification that a quotient presenting a fine moduli problem for quaternionic data is flat and locally of finite type once $2$ and $3$ are invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (n : ℕ) (hn : IsUnit ((n : ℕ) : 𝒪)) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : IsDedekindDomain B₀) (i : B₀ →+* 𝒪),
      Flat (Spec.map (CommRingCat.ofHom i)) ∧ IsUnit ((n : ℕ) : B₀) := by sorry
