-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/8e1aaa82-222f-56a7-a5aa-460e054263bd
-- title:
--   Genus-zero Riemann–Roch: L(E-w) is properly contained in L(E)
-- statement:
--   Let $k$ be an algebraically closed field and let $F$ be a field equipped with a $k$-algebra structure. Assume given a ring isomorphism $e \colon \mathrm{RatFunc}(k) \to F$ which is compatible with the two structure maps from $k$, in the sense that $e(\iota(c)) = \iota_F(c)$ for every $c \in k$; thus $F$ is $k$-isomorphic to the rational function field in one variable over $k$. Here a place of $F$ over $k$ is a valuation subring of $F$ that contains the image of $k$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, and its degree is $\sum_v E(v)\,\deg v$, the sum of its coefficients weighted by the degrees $\deg v$ of the places. For a divisor $E$ with $\deg E \ge 0$ and any place $w$, the assertion is that there is an element $p$ of the Riemann–Roch space $L(E)$, that is, an element of $F$ with $v(p) \le \exp(E(v))$ for the $\mathbb{Z}^{m0}$-valued adic valuation attached to every place $v$ (equivalently $\operatorname{ord}_v(p) \ge -E(v)$ for all $v$), which does not lie in $L(E - \delta_w)$, where $\delta_w$ is the divisor taking the value $1$ at $w$ and $0$ elsewhere. Since the inclusion $L(E-\delta_w) \subseteq L(E)$ always holds, this says the inclusion is strict: some $p \in L(E)$ has order exactly $-E(w)$ at $w$.
--
--   This is the sharp form of Riemann–Roch for the projective line: for $\deg E \ge 0$ the dimension of $L(E)$ drops by exactly one upon subtracting a single place, with no hypothesis distinguishing the finite places from the place at infinity. It is used in the construction of functions on a rational base with prescribed exact orders at a given place, via [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) (hE : 0 ≤ E.degree) (w : Place k F) :
    ∃ p ∈ riemannRochSpace E, p ∉ riemannRochSpace (E - Finsupp.single w 1) := by sorry
