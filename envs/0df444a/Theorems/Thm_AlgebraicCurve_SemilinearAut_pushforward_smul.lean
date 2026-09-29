-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforward_smul
-- name    : AlgebraicCurve.SemilinearAut.pushforward_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/279a0daf-12c9-5f47-8ead-90a3a84d9221
-- title:
--   Divisor pushforward commutes with intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and assume $F'$ is integral over $F$. Here a semilinear automorphism in `SemilinearAut K F` is a pair consisting of a ring automorphism of $F$ and a ring automorphism of $K$ that are compatible with $\mathrm{algebraMap}\,K\,F$, these pairs forming a subgroup of $\mathrm{RingAut}(F)\times\mathrm{RingAut}(K)$, and similarly for $F'$; a place in `Place K F'` is a valuation subring of $F'$ containing the image of $K$, different from all of $F'$, and a principal ideal ring, while a divisor in `Divisor K F'` is a finitely supported function from such places to $\mathbb{Z}$. Given $g \in$ `SemilinearAut K F` and $g' \in$ `SemilinearAut K F'` that are intertwined along $\mathrm{algebraMap}\,F\,F'$, meaning $g' \cdot (\iota x) = \iota (g \cdot x)$ for every $x \in F$ where $\iota = \mathrm{algebraMap}\,F\,F'$, and given a divisor $D$ on $F'$, the assertion is that $\mathrm{pushforward}(g' \cdot D) = g \cdot \mathrm{pushforward}(D)$, where `Divisor.pushforward` is the additive map sending the divisor concentrated at a place $w$ of $F'$ with multiplicity $n$ to the divisor concentrated at the restricted place $w|_F$ (the preimage valuation subring under $\iota$) with multiplicity $n \cdot f(w)$, $f(w)$ being the residue degree $[\,\kappa(w) : \kappa(w|_F)\,]$, and the actions on divisors are those induced by the actions of $g$ and $g'$ on places.
--
--   This is the equivariance of the norm (pushforward) map on divisors of an extension of fields, in the setting of places of a field over a base field, with respect to a compatible pair of semilinear automorphisms of the two fields. It is used to derive the corresponding statement [`AlgebraicCurve.SemilinearAut.pushforwardAlong_smul`](thm.html#AlgebraicCurve.SemilinearAut.pushforwardAlong_smul) formulated along an explicit embedding rather than via an algebra instance.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pushforward_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.pushforward_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by sorry
