-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive
-- name    : AlgebraicCurve.RationalFunctionField.mapDomain_eq_ord_div_map_of_primitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/cec6aa21-e38b-5803-b60d-a18d6d2a8109
-- title:
--   Reduction of principal divisors on the projective line
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $k$ a field, and $\mathrm{red} \colon A \to k$ a ring homomorphism killing the maximal ideal of the local ring $A$. Let $\mathrm{sp}$ be any function from the places of $L(t)$ over $L$ to the places of $k(t)$ over $k$ (a place being a valuation subring, distinct from the whole field, containing the image of the constants and having principal ideals) such that: for $a \in A$, $\mathrm{sp}$ sends the place of the point $t = a$ (the finite place attached to the irreducible $X - a$) to the place of the point $t = \mathrm{red}(a)$; for $a \in L$ with $a \notin A$, $\mathrm{sp}$ sends the place of $t = a$ to the place at infinity of $k(t)$; and $\mathrm{sp}$ sends the place at infinity of $L(t)$ to that of $k(t)$. Let $P, Q \in A[X]$ each have some coefficient outside the maximal ideal of $A$, and let $D$ be a finitely supported integer-valued function on the places of $L(t)$ whose value at every place $w$ is $\operatorname{ord}_w$ of the rational function $P/Q$ obtained by pushing $P$ and $Q$ into $L[X] \subseteq L(t)$, where $\operatorname{ord}_w$ denotes minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation of $w$. Then for every place $v'$ of $k(t)$ over $k$, the push-forward $\mathrm{Finsupp.mapDomain}\ \mathrm{sp}\ D$ evaluated at $v'$ — that is, the sum of the $D(w)$ over the places $w$ with $\mathrm{sp}(w) = v'$ — equals $\operatorname{ord}_{v'}$ of the rational function $\bar P/\bar Q \in k(t)$, where $\bar P, \bar Q \in k[X]$ are the coefficientwise images of $P, Q$ under $\mathrm{red}$.
--
--   This is Deuring's principle that the reduction of a principal divisor is the divisor of the reduction, in the genus-zero case of the projective line with the constant (Gauss) reduction: integral zeros and poles specialise to their images, while non-integral ones and the point at infinity collapse to the point at infinity downstairs, multiplicities adding; the primitivity hypotheses on $P$ and $Q$ guarantee in particular that $\bar P$ and $\bar Q$ are nonzero. It is used in the place-specialisation machinery, by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.orderLawFixed) and [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.RationalFunctionField.mapDomain_eq_ord_div_map_of_primitive
    {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)] {A : ValuationSubring L}
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] (red : A →+* k)
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (sp : Place L (RatFunc L) → Place k (RatFunc k))
    (hsp_int : ∀ a : A, sp (placeOfPoint L (a : L)) = placeOfPoint k (red a))
    (hsp_out : ∀ a : L, a ∉ A → sp (placeOfPoint L a) = placeInfty k)
    (hsp_infty : sp (placeInfty L) = placeInfty k)
    (P Q : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A)
    (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A)
    (D : Divisor L (RatFunc L))
    (hD : ∀ w, D w = w.ord (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
                              / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))) :
    ∀ v' : Place k (RatFunc k),
      Finsupp.mapDomain sp D v'
        = v'.ord (algebraMap (Polynomial k) (RatFunc k) (P.map red)
                  / algebraMap (Polynomial k) (RatFunc k) (Q.map red)) := by sorry
