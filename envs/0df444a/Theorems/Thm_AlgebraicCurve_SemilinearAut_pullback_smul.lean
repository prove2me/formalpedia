-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pullback_smul
-- name    : AlgebraicCurve.SemilinearAut.pullback_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/692fbc6d-f8d3-5272-97b9-35c89022a665
-- title:
--   Divisor pullback commutes with intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and assume $F'$ is integral over $F$. A semilinear automorphism of $F$ over $K$ is a pair $(\sigma,\tau)$ consisting of a ring automorphism of $F$ and one of $K$ such that $\sigma(\iota_K a)=\iota_K(\tau a)$ for all $a\in K$, where $\iota_K$ is the structure map; let $g$ be such a pair for $F$ and $g'$ one for $F'$. Assume the class `HasPrincipalDivisors K F'`, i.e. every nonzero $f\in F'$ admits a finitely supported divisor on the places of $F'$ whose coefficient at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$; here a place of $F'$ over $K$ is a proper valuation subring containing the image of $K$ which is a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Assume further that $g$ and $g'$ intertwine along the structure map $F\to F'$: $g'\cdot(\iota x)=\iota(g\cdot x)$ for all $x\in F$. Then for every divisor $D$ on the places of $F$ over $K$, the pullback to $F'$ of $g\cdot D$ equals $g'\cdot$ (the pullback of $D$), the pullback being the additive map sending a place $v$ with coefficient $n$ to $\sum_{w\mid v} n\,e(w/v)\,[w]$.
--
--   This is the equivariance of the conorm (divisor pullback) map for a compatible pair of semilinear automorphisms of $F$ and $F'$: such automorphisms permute places, preserving fibres and ramification indices. It is used to obtain the corresponding statement [`AlgebraicCurve.SemilinearAut.pullbackAlong_smul`](thm.html#AlgebraicCurve.SemilinearAut.pullbackAlong_smul) for pullback along an explicit $K$-algebra embedding, in the treatment of divisors and correspondences on curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pullback_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.pullback_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F) : Divisor.pullback F' (g • D) = g' • Divisor.pullback F' D := by sorry
