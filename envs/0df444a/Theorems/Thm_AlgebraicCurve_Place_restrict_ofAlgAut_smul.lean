-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul
-- name    : AlgebraicCurve.Place.restrict_ofAlgAut_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2e110162-9aa0-5bc2-a7ac-8b8e54efc63f
-- title:
--   F'-automorphisms fix restrictions of places to F'
-- statement:
--   Let $K \subseteq F' \subseteq M$ be fields, given as a field $K$, a field $F'$ with a $K$-algebra structure, a field $M$ with $K$- and $F'$-algebra structures forming a scalar tower over $K$, with $M$ integral over $F'$. Let $\sigma$ be an $F'$-algebra automorphism of $M$, and let $W$ be a place of $M$ over $K$ in the project's sense: a valuation subring $\mathcal{O}_W \subseteq M$ containing the image of $K$, different from $M$ itself, and whose underlying ring is a principal ideal ring. Viewing $\sigma$ as a $K$-algebra automorphism and hence, via `SemilinearAut.ofAlgAut`, as the semilinear automorphism given by the pair $(\sigma, \mathrm{id}_K)$ of ring automorphisms of $M$ and of $K$ compatible with $K \to M$, let $\sigma \cdot W$ be the place whose valuation subring is the pointwise image $\sigma(\mathcal{O}_W)$. The assertion is that the restrictions to $F'$ of $\sigma \cdot W$ and of $W$ coincide as places of $F'$ over $K$, i.e. $\sigma(\mathcal{O}_W)$ and $\mathcal{O}_W$ have the same preimage in $F'$ under $F' \to M$.
--
--   This is the standard fact that an automorphism of $M$ fixing an intermediate field $F'$ carries each place of $M$ to a place lying over the same place of $F'$, so that the fibres of restriction are unions of orbits. It is used in the treatment of the Galois action on places and divisors, notably in the identity expressing the sum of the Galois translates of a divisor as a pullback of a pushforward and in the injectivity results for the divisorial Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrict_ofAlgAut_smul {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [Algebra.IsIntegral F' M] (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by sorry
