-- Prove2me | Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_natCast_mem_pow
-- name    : FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/c2d61378-7689-5df0-a9d5-60c2225fa052
-- title:
--   A Drinfeld basis of level q in I forces q∈ I^{q^2-1}
-- statement:
--   Let $T$ be a commutative ring and $I\subseteq T$ an ideal such that $T$ is $I$-adically complete (and $I$-adically separated), let $F$ be a formal group law over $T$, let $q$ be a natural number and let $x_0,x_1$ be elements of $I$. Assume `F.IsDrinfeldBasisAdic I q x₀ x₁`, that is: equipping $T$ with the $I$-adic topology, there is a unit $u$ in the ring $T[[Z]]$ of one-variable power series with $$F.\mathrm{nthSeries}\,q \;=\; u\cdot F.\mathrm{drinfeldDivisor}\,q\,x_0\,x_1,$$ the $q$-fold addition series of $F$ (whose coefficient in degree $1$ is $q\cdot 1_T$, by [`FormalGroup.coeff_one_nthSeries`](thm.html#FormalGroup.coeff_one_nthSeries)) being the unit multiple of the Drinfeld divisor attached to the pair $(x_0,x_1)$ at level $q$; the latter is, as the proof records, the monic product $\prod_{(a,b)\in\{0,\dots,q-1\}^2}\bigl(Z-([a]x_0+_F[b]x_1)\bigr)$ of $q^2$ linear factors indexed by pairs of residues below $q$. The conclusion is that $q\cdot 1_T$ lies in $I^{\,q\cdot q-1}$.
--
--   This is the standard numerical constraint imposed on a ring by the existence of a full Drinfeld basis of level $q$ for a formal group over it: the $q^2$ points of the basis are congruent to $0$, so the linear coefficient $q$ of $[q]_F$ is a product of $q^2-1$ elements of $I$. It is used in [`FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm), where it forces $q$ into the square of the maximal ideal of the relevant deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsDrinfeldBasisAdic_natCast_mem_pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) (q : ℕ)
    (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    (q : T) ∈ I ^ (q * q - 1) := by sorry
