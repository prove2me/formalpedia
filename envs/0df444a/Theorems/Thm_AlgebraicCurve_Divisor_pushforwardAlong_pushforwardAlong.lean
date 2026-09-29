-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
-- name    : AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bd1d7d23-52ed-54d1-b5fa-449c84c904d3
-- title:
--   Functoriality of divisor push-forward along composites
-- statement:
--   Let $K$, $F$, $F'$, $F''$ be fields, each of $F$, $F'$, $F''$ equipped with a $K$-algebra structure, let $\varphi \colon F \to F'$ and $\chi \colon F' \to F''$ be $K$-algebra homomorphisms, and assume that the underlying ring homomorphisms of $\varphi$, of $\chi$, and of the composite $\chi \circ \varphi$ are integral (the last being assumed separately, not deduced). Let $D$ be a divisor of $F''$ over $K$, that is, a finitely supported function with values in $\mathbb{Z}$ on the set of places of $F''$ over $K$, a place being a valuation subring of $F''$ that contains the image of $K$, is not all of $F''$, and is a principal ideal ring. Then pushing $D$ forward along $\chi$ and then pushing the result forward along $\varphi$ gives the same divisor of $F$ over $K$ as pushing $D$ forward along $\chi \circ \varphi$. Here the push-forward along an integral $K$-algebra map is the additive map that sends a place $W$ of the larger field, with multiplicity $n$, to its restriction to the smaller field with multiplicity $n$ times the inertia degree of $W$ over that restriction.
--
--   This is the transitivity (functoriality) of the push-forward of divisors in a tower of integral extensions of function fields over $K$, reflecting the multiplicativity of residue degrees in towers. It is used throughout the theory of divisor correspondences, for instance in the composition law for correspondences and in comparisons of a correspondence with a scalar multiple of another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') : Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by sorry
