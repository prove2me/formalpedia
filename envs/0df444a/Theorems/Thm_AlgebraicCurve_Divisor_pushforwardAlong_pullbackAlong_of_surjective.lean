-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
-- name    : AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/9ea7dcdf-afac-5f3a-b946-8c0595baa5c8
-- title:
--   Pushforward after pullback along a surjection is the identity
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ both $K$-algebras, and assume $F'$ satisfies `HasPrincipalDivisors` over $K$, i.e. every nonzero $f \in F'$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ of $F'$ over $K$ and $\deg D = 0$. Here a place of a function field is a valuation subring containing the image of $K$, different from the whole field, and a principal ideal ring; a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring homomorphism is integral, and suppose in addition that $\varphi$ is surjective. Then for every divisor $D$ on $F$ one has $\varphi_*(\varphi^* D) = D$, where $\varphi^*$ and $\varphi_*$ are the pullback and pushforward of divisors taken along the $F$-algebra structure that $\varphi$ puts on $F'$: $\varphi^*$ sends a place $v$ of $F$ to the sum of its ramification indices over the places of $F'$ in the fibre above $v$, and $\varphi_*$ sends a place $w$ of $F'$ to its inertia degree times its restriction to $F$.
--
--   This is the divisor-theoretic statement that an isomorphism of function fields induces mutually inverse maps on divisor groups: surjectivity forces the extension along $\varphi$ to have degree $1$. It is used in the treatment of correspondences on curves, for instance in the compatibility of correspondences with the action of $K$-algebra automorphisms and in the construction of roof data on degree-zero divisor class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D : AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ (AlgebraicCurve.Divisor.pullbackAlong φ hφ D) = D := by sorry
