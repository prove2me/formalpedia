-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul
-- name    : AlgebraicCurve.SemilinearAut.pushforwardAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5d53581b-7667-5a31-86f1-d5b162be56bb
-- title:
--   Equivariance of divisor pushforward along an embedding
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$. Recall that an element of `SemilinearAut K F` is a pair $(\sigma,\tau)$ consisting of a ring automorphism $\sigma$ of $F$ and a ring automorphism $\tau$ of $K$ with $\sigma(\mathrm{alg}_K^F(a)) = \mathrm{alg}_K^F(\tau a)$ for all $a \in K$, these pairs forming a subgroup of $\mathrm{Aut}(F) \times \mathrm{Aut}(K)$; such pairs act on the group `Divisor K F` of finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $K$ (a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring). Fix $g \in$ `SemilinearAut K F` and $g' \in$ `SemilinearAut K F'`. Let $\varphi : F \to F'$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, so that `Divisor.pushforwardAlong φ hφ` is the additive map `Divisor K F' →+ Divisor K F` sending a place $w$ of $F'$ to its restriction to $F$ weighted by the inertia degree of $w$ over $F$. Assume $g$ and $g'$ intertwine along $\varphi$, that is $g' \cdot \varphi(x) = \varphi(g \cdot x)$ for every $x \in F$. Then for every divisor $D$ on $F'$ one has $\varphi_*(g' \cdot D) = g \cdot \varphi_*(D)$.
--
--   This is the equivariance of the divisor pushforward under a pair of semilinear automorphisms intertwined along an explicit embedding, stated for a $K$-algebra map $\varphi$ rather than for a fixed scalar-tower algebra structure. It is used for the induced action on degree-zero divisor classes and on correspondences, and in the comparison of Hecke and $\mathrm{GL}_2$ actions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.pushforwardAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F') : Divisor.pushforwardAlong φ hφ (g' • D) = g • Divisor.pushforwardAlong φ hφ D := by sorry
