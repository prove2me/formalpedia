-- Prove2me | Theorems.Thm_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
-- name    : AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a1ee135e-8275-5366-8067-e856eaf2f278
-- title:
--   Cotangent functionals of an augmentation and lifts to the trivial square-zero extension
-- statement:
--   Let $\mathcal{O}$ and $R$ be commutative rings with $R$ an $\mathcal{O}$-algebra, and let $\pi_R : R \to \mathcal{O}$ be a homomorphism of $\mathcal{O}$-algebras (an augmentation). Let $N$ be an additive commutative group carrying a left $\mathcal{O}$-module structure and a left $\mathcal{O}^{\mathrm{op}}$-module structure which agree (the `IsCentralScalar` condition), so that the trivial square-zero extension `TrivSqZeroExt 𝒪 N`, i.e. $\mathcal{O} \oplus N$ with multiplication $(a,m)(b,n) = (ab, a\cdot n + b\cdot m)$, is an $\mathcal{O}$-algebra. Let $I = \ker \pi_R$ and let $f : I/I^2 \to N$ be an $\mathcal{O}$-linear map on the cotangent module `(RingHom.ker πR).Cotangent`. The assertion is that there is exactly one $\mathcal{O}$-algebra homomorphism $\psi : R \to \mathcal{O} \oplus N$ such that, first, the first component of $\psi(r)$ equals $\pi_R(r)$ for every $r \in R$, and second, for every $a \in I$ the second component of $\psi(a)$ equals $f$ applied to the class of $a$ in $I/I^2$ (the image of $a$ under `Submodule.toCotangent`).
--
--   This is the "functionals give lifts" half of the standard dictionary between $\mathcal{O}$-linear maps out of the cotangent module $I/I^2$ of an augmentation and $\mathcal{O}$-algebra maps into a trivial square-zero extension; when $\mathcal{O}$ is a field it identifies the tangent space at a closed point with the dual of the cotangent space. It is used by the tangent-space computations for schemes and for the smoothness/dimension arguments in the Čerednik–Drinfel'd and Jacobian good-reduction parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v x

theorem AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N) :
    ∃! ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N, (∀ r : R, (ψ r).fst = πR r) ∧
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by sorry
