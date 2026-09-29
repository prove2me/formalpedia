-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_finite_setOf_card_fiberAlong_ne_finrankAlong
-- name    : AlgebraicCurve.Place.finite_setOf_card_fiberAlong_ne_finrankAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/cbac2c5e-d2d9-56ba-bf76-92d9a89aa294
-- title:
--   Almost all places of a curve have full fibre
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $F$, $F'$ be fields equipped with $K$-algebra structures, each satisfying `IsCurveOver K` — that is, every nonzero function has a principal divisor of degree $0$, every place has residue field finite over $K$, and the module of Kähler differentials over $K$ is free of rank $1$ — and each essentially of finite type over $K$. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and assume `FiniteAlong K φ`, i.e. that $F'$ is a finite module over $F$ for the $F$-algebra structure on $F'$ induced by $\varphi$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Then the set of places $P$ of $F$ for which the fibre `Place.fiberAlong φ hφ P`, the finite set of places of $F'$ whose restriction along $\varphi$ is $P$, has cardinality different from `finrankAlong K φ`, the $F$-dimension of $F'$, is finite.
--
--   This is the finiteness of the ramification locus of a finite cover of curves in characteristic zero, stated in the fibre-counting form: all but finitely many places of the base have a fibre of the maximal possible cardinality $[F':F]$, equivalently (by [`AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff`](thm.html#AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff)) are unramified in $F'$. It is used in the Čerednik–Drinfeld part of the development to compare degrees of maps in a tower of moduli curves with ranks of the corresponding field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_finite_setOf_card_fiberAlong_ne_finrankAlong.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.finite_setOf_card_fiberAlong_ne_finrankAlong
    {K F F' : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    {P : Place K F | (Place.fiberAlong φ hφ P).card ≠ finrankAlong K φ}.Finite := by sorry
