-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2a3c5180-98ac-539a-9346-857c4bf9fa4e
-- title:
--   Twisted Lagrange interpolation in L(E) on a rational function field
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field extension of $k$ (as a $k$-algebra) together with a ring isomorphism $e : k(X) \xrightarrow{\sim} F$ that is compatible with the two structure maps from $k$, i.e. $e(\mathrm{alg}_k(c)) = \mathrm{alg}_k(c)$ for all $c \in k$. Let $\iota$ be a finite index type and let $E$ be a divisor of $F/k$, that is, a finitely supported integer-valued function on the places of $F/k$, a place being a valuation subring of $F$ containing the image of $k$, different from $F$ itself and a principal ideal ring; assume $\#\iota \le \deg E + 1$, where $\deg E = \sum_v E(v)\,\deg v$. Let $a : \iota \to k$ be injective and let $c : \iota \to k$ be arbitrary. Then there is an element $p$ of the Riemann–Roch space $L(E) = \{f \in F : v(f) \le \exp(E(v)) \text{ for every place } v\}$ (the adic valuation taken with values in $\mathbb{Z}^{m0}$) such that for every $i$, writing $v_i$ for the place of $F$ obtained by transporting along $e$ the place of $k(X)$ attached to the point $a_i$ (the one cut out by the irreducible polynomial $X - a_i$), the element $e(X - a_i)^{E(v_i)} \cdot p$ lies in the valuation ring of $v_i$ and its residue is the image of $c_i$ in the residue field of $v_i$.
--
--   This is twisted Lagrange interpolation on the projective line: after clearing the prescribed poles by the local uniformisers $X - a_i$, prescribing the values $c_i$ at $\#\iota \le \deg E + 1$ distinct points is possible within $L(E)$, which in genus $0$ amounts to surjectivity of evaluation of polynomials of bounded degree at distinct points. It is used in the construction of prolongations of places on modular curves, where it supplies sections of a divisor with prescribed twisted values at finitely many points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    {ι : Type*} [Fintype ι]
    (E : Divisor k F) (hE : (Fintype.card ι : ℤ) ≤ E.degree + 1)
    (a : ι → k) (ha : Function.Injective a) (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i,
      (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i))).HasValue
        (e (RatFunc.X - RatFunc.C (a i)) ^
            (E (Place.congrEquiv e he (RationalFunctionField.placeOfPoint k (a i)))) * p)
        (c i) := by sorry
