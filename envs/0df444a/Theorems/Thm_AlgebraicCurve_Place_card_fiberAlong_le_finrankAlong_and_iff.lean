-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff
-- name    : AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/343434e6-233a-5d1e-8480-62e6925724a3
-- title:
--   Fibre size bounded by degree, with equality iff unramified
-- statement:
--   Let $K$ be an algebraically closed field and let $F$, $F'$ be fields equipped with $K$-algebra structures that are essentially of finite type over $K$ and satisfy `IsCurveOver K ·`: every nonzero element has a principal divisor of degree $0$, every place has residue field finite over $K$, and the module of Kähler differentials $\Omega[F\,/\,K]$ is free of rank one. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism, and view $F'$ as an $F$-algebra via $\varphi$; assume $\varphi$ is integral, that $F'$ is a finite $F$-module, and that $F'$ is separable over $F$. Fix a place $P$ of $F$ over $K$. Then the (finite) set of places $W$ of $F'$ over $K$ whose restriction along $\varphi$ is $P$ has cardinality at most $\operatorname{finrank}_F F'$, and this cardinality equals $\operatorname{finrank}_F F'$ if and only if every such $W$ has ramification index one along $\varphi$, the ramification index being the least $n > 0$ for which $W.\mathrm{ord}(\varphi f) = n$ for some $f \neq 0$ in $F$.
--
--   This is the classical count of points in a fibre of a finite separable morphism of curves over an algebraically closed field: at most $\deg \varphi$ points, with equality exactly at the unramified fibres. It is used to show that the set of places of $F$ whose fibre has fewer than $\operatorname{finrank}_F F'$ points is finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (P : Place K F) :
    (Place.fiberAlong φ hφ P).card ≤ finrankAlong K φ ∧
      ((Place.fiberAlong φ hφ P).card = finrankAlong K φ ↔
        ∀ W ∈ Place.fiberAlong φ hφ P, W.ramificationIndexAlong φ = 1) := by sorry
