-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
-- name    : AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/32067690-0f12-5f1f-a585-99eaa8e628de
-- title:
--   Restriction along a Frobenius-type endomorphism is a twist
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $p$ be a natural number with $p \neq 0$, and let $g$ be an element of `SemilinearAut K L`, that is, a pair consisting of a ring automorphism of $L$ and a ring automorphism of $K$ that are compatible with the structure map $K \to L$. Let $\Phi \colon L \to L$ be a $K$-algebra homomorphism whose underlying ring homomorphism is integral, and assume $\Phi(f) = (g^{-1} \cdot f)^p$ for every $f \in L$. Then for every place $w$ of $L$ over $K$ — a valuation subring of $L$ containing the image of $K$, different from $L$ itself, and a principal ideal ring — the restriction of $w$ along $\Phi$, whose valuation subring is the preimage $\Phi^{-1}(\mathcal{O}_w)$ under the algebra structure on $L$ induced by $\Phi$, coincides with the place $g \cdot w$ obtained by transporting $w$ by the pointwise action of the automorphism component of $g$ on valuation subrings.
--
--   This is the field-theoretic core of the identification of the geometric Frobenius correspondence on a curve with the twist of places by the corresponding arithmetic (constant-field) Frobenius: restricting a place along an endomorphism which is a $p$-th power composed with a semilinear automorphism simply twists the place. It is used in the modular-curve part of the development, for instance in transporting Kähler differentials and pole orders along a Frobenius semilinear map for $q$-expansion function fields, and in computing the image of the Frobenius place map on the places attached to $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (p : ℕ) (hp : p ≠ 0) (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦi : Φ.toRingHom.IsIntegral) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p)
    (w : AlgebraicCurve.Place K L) :
    w.restrictAlong Φ hΦi = g • w := by sorry
