-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
-- name    : AlgebraicCurve.SemilinearAut.restrict_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/358d7b39-9a63-5e7c-be46-bfb08b48b74c
-- title:
--   Equivariance of restriction of places under intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, and with $F'$ integral over $F$. Let $g$ be a semilinear automorphism of $F$ over $K$, that is, a pair consisting of a ring automorphism of $F$ and a ring automorphism of $K$ compatible with $\mathrm{algebraMap}\,K\,F$, and let $g'$ be such a pair for $F'$ over $K$. Assume $g$ and $g'$ are intertwined along $\mathrm{algebraMap}\,F\,F'$, i.e. $g' \cdot (\mathrm{algebraMap}\,F\,F')(x) = (\mathrm{algebraMap}\,F\,F')(g \cdot x)$ for every $x \in F$, where a semilinear automorphism acts through its automorphism of the relevant field. Let $w$ be a place of $F'$ over $K$, i.e. a valuation subring of $F'$ containing the image of $K$, distinct from $F'$ itself, and a principal ideal ring. Then the restriction to $F$ of $g' \cdot w$, namely the preimage of the valuation subring under $\mathrm{algebraMap}\,F\,F'$, equals $g$ applied to the restriction of $w$ to $F$.
--
--   This is the compatibility of restriction of places in an algebraic extension with the action of automorphisms intertwined along that extension. It underlies the equivariance of pullback and pushforward of divisors for semilinear automorphisms, and is used in the treatment of Hecke operators and the Galois action on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_restrict_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.restrict_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).restrict F = g • (w.restrict F) := by sorry
