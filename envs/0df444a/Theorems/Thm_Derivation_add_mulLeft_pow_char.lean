-- Prove2me | Theorems.Thm_Derivation_add_mulLeft_pow_char
-- name    : Derivation.add_mulLeft_pow_char
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/cb901164-68b9-5426-ac9a-e0a1d410102f
-- title:
--   Hochschild's formula for (d+a)ᵖ in characteristic p
-- statement:
--   Let $R$ and $F$ be commutative rings with $F$ an $R$-algebra, let $p$ be a prime number, and assume $F$ has characteristic $p$. Let $d \colon F \to F$ be an $R$-derivation of $F$ into itself, and let $a \in F$. Write $d$ also for the underlying $R$-linear map `d.toLinearMap` of $F$, and let `LinearMap.mulLeft R a` be the $R$-linear multiplication operator $x \mapsto a x$. The assertion is an identity between $R$-linear endomorphisms of $F$, powers being taken with respect to composition in the endomorphism ring: the $p$-th power of $d + (x \mapsto ax)$ equals the $p$-th power of $d$ plus the multiplication operator attached to the single element $a^p + d^{p-1}(a)$, where $d^{p-1}$ is the $(p-1)$-fold composite of $d$ applied to $a$. In symbols,
--   $$(d + M_a)^p = d^p + M_{a^p + d^{p-1}(a)}, \qquad M_b(x) = bx .$$
--
--   This is Hochschild's identity for the $p$-th power of a derivation twisted by a multiplication operator; the element $a^p + d^{p-1}(a)$ is the $p$-curvature of the rank-one connection $d + a$. It is used in the study of the Cartier operator on a curve in characteristic $p$, via [`AlgebraicCurve.exists_dlog_of_cartierOperator_fixed`](thm.html#AlgebraicCurve.exists_dlog_of_cartierOperator_fixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Derivation_add_mulLeft_pow_char.lean

import Mathlib.RingTheory.Derivation.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v

theorem Derivation.add_mulLeft_pow_char {R : Type u} {F : Type v} [CommRing R] [CommRing F]
    [Algebra R F] (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a) := by sorry
