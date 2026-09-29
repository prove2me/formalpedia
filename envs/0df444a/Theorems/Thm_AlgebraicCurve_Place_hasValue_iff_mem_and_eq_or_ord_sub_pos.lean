-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
-- name    : AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/2d3868f1-f2da-598a-9b17-2d6883b44475
-- title:
--   HasValue criterion via integrality and order of g-c
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $v$ be a place of $L$ over $K$: a valuation subring $\mathcal O_v$ of $L$ which contains the image of $K$ under the structure map, is not all of $L$, and is a principal ideal ring. Let $g \in L$ and $c \in K$. The assertion is an equivalence between two formulations of "$g$ takes the value $c$ at $v$". The left-hand side, `v.HasValue g c`, says that $g$ lies in $\mathcal O_v$ and that the image of $g$ under the residue map $\mathcal O_v \to \mathcal O_v/\mathfrak m_v$ equals the image of $c$ under the induced map from $K$ to the residue field of $\mathcal O_v$. The right-hand side says that $g \in \mathcal O_v$ and, in addition, either $g$ is exactly the image of $c$ in $L$, or $0 < v.\mathrm{ord}(g - \mathrm{algebraMap}\,K\,L\,c)$, where $v.\mathrm{ord}$ is minus the logarithm of the $\mathbb Z^{m0}$-valued adic valuation attached to the height-one prime of $\mathcal O_v$. The disjunction is needed because that normalisation of $\mathrm{ord}$ assigns the value $0$ to $0$.
--
--   This is the bookkeeping bridge between the residue-field formulation of "value at a place" and the order-of-vanishing formulation, used throughout the treatment of places and divisors on the modular curves; some thirty-eight later results on place specialisation and representatives of divisor classes invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by sorry
