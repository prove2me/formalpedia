-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
-- name    : AlgebraicCurve.Pic0.forall_isPrincipal_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8a7a1a6d-284d-5da2-aa09-d62223fb7e71
-- title:
--   Principality of degree-zero divisors transports along base-compatible isomorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$. Suppose given a ring isomorphism $e : F \simeq F'$ which is compatible with the two $K$-algebra structures, in the sense that $e(\mathrm{algebraMap}\,a) = \mathrm{algebraMap}\,a$ for every $a \in K$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose ring is a principal ideal ring; a divisor is a finitely supported function $D$ from places to $\mathbb{Z}$; its degree is $\sum_v D(v)\cdot \deg v$, with $\deg v$ the integer attached to the place $v$ by `Place.deg`; and $D$ is principal when there exists $f \in F$, $f \neq 0$, with $D(v) = \mathrm{ord}_v(f)$ for every place $v$, where $\mathrm{ord}_v$ is the order function `Place.ord`. The hypothesis is that every divisor of $F/K$ of degree $0$ is principal. The conclusion is that a given divisor $D'$ of $F'/K$ of degree $0$ is principal, i.e. of the form $v \mapsto \mathrm{ord}_v(f')$ for some nonzero $f' \in F'$.
--
--   This is the transport of the statement "$\mathrm{Pic}^0$ is trivial", in the pointwise form "every degree-zero divisor is principal", along an isomorphism of function fields over the same base field $K$. It is used to move the triviality of the divisor class group from a concrete model of a genus-zero curve to another presentation of its function field, and is cited in the treatment of Hecke operators and the Fricke involution on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.forall_isPrincipal_of_ringEquiv {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal)
    (D' : Divisor K F') (hD' : Divisor.degree D' = 0) :
    D'.IsPrincipal := by sorry
