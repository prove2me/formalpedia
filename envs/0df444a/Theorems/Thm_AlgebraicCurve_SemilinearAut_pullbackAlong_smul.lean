-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
-- name    : AlgebraicCurve.SemilinearAut.pullbackAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ecb7a4aa-51cd-56e4-a420-e8f3bdd5984b
-- title:
--   Equivariance of divisor pull-back along an embedding
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$, and let $g$ and $g'$ be semilinear automorphisms of $F/K$ and of $F'/K$ respectively; here a semilinear automorphism of $F/K$ is a pair $(\sigma,\tau)$ consisting of a ring automorphism of $F$ and one of $K$ satisfying $\sigma(\iota a)=\iota(\tau a)$ for all $a \in K$, $\iota$ the structure map, these pairs forming a subgroup of $\mathrm{Aut}(F)\times\mathrm{Aut}(K)$. Assume $F'$ has principal divisors over $K$, i.e. every nonzero $f \in F'$ admits a finitely supported $D : \mathrm{Place}(K,F') \to \mathbb{Z}$ with $D(v)=\mathrm{ord}_v(f)$ at every place and $\deg D = 0$, where a place of $F'/K$ is a valuation subring of $F'$ containing the image of $K$, distinct from $F'$, and a principal ideal ring. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring map is integral, and suppose $g$ and $g'$ are intertwined along $\varphi$, in the sense that $g' \cdot \varphi(x) = \varphi(g \cdot x)$ for all $x \in F$. Then for every divisor $D$ on $F/K$ one has $\varphi^*(g \cdot D) = g' \cdot \varphi^*(D)$, where $\varphi^*$ is the additive pull-back map $\mathrm{Divisor}(K,F) \to \mathrm{Divisor}(K,F')$ attached to $\varphi$ and its integrality.
--
--   This is the equivariance of the divisor pull-back along an explicit integral embedding of function fields under a pair of intertwined semilinear automorphisms, stated for the pull-back indexed by the morphism $\varphi$ rather than by an ambient algebra structure. It feeds the semilinear equivariance of correspondences and of the degree-zero Picard group, and through these the construction of Galois-equivariant maps on Tate modules of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.pullbackAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F) : Divisor.pullbackAlong φ hφ (g • D) = g' • Divisor.pullbackAlong φ hφ D := by sorry
