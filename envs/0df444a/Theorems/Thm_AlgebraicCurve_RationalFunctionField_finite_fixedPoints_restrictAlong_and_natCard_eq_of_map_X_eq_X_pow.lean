-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
-- name    : AlgebraicCurve.RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/34607be7-6594-5857-b06b-af5eca19889d
-- title:
--   The q-Frobenius on K(X) has exactly q+1 fixed places
-- statement:
--   Let $K$ be an algebraically closed field, let $q$ be a natural number with $1 < q$ whose image in $K$ is $0$, and let $\varphi \colon \mathrm{RatFunc}\,K \to \mathrm{RatFunc}\,K$ be a $K$-algebra endomorphism of the rational function field whose underlying ring homomorphism is integral and which satisfies $\varphi(X) = X^{q}$. A place of $\mathrm{RatFunc}\,K$ over $K$ is, in the sense used here, a valuation subring of $\mathrm{RatFunc}\,K$ that contains the image of $K$ under the structure map, is not the whole field, and is a principal ideal ring. Using $\varphi$ to regard $\mathrm{RatFunc}\,K$ as an algebra over itself, [`AlgebraicCurve.Place.restrictAlong`](def/AlgebraicCurve_Correspondence.html#L204) sends a place $w$ to the place whose valuation subring is the preimage $\varphi^{-1}(\mathcal O_w)$, the hypothesis of integrality guaranteeing that this preimage is again such a place. The theorem asserts that the set of places $w$ with $\varphi^{-1}(\mathcal O_w) = \mathcal O_w$ is finite and that its cardinality is exactly $q + 1$.
--
--   Geometrically these fixed places are the $\mathbb F_q$-rational points of the projective line: the places $X = a$ with $a^{q} = a$ together with the place at infinity, giving the classical count $N(\mathbb F_q(t)) = q+1$ for the rational function field. It supplies the base case of the correspondence count used in [`AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places`](thm.html#AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
    (K : Type*) [Field K] [IsAlgClosed K] (q : ℕ) (hq : 1 < q) (hqK : (q : K) = 0)
    (φ : RatFunc K →ₐ[K] RatFunc K) (hφi : φ.toRingHom.IsIntegral)
    (hφ : φ RatFunc.X = RatFunc.X ^ q) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)) = q + 1 := by sorry
