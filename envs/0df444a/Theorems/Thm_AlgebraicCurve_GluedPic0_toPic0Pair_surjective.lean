-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_toPic0Pair_surjective
-- name    : AlgebraicCurve.GluedPic0.toPic0Pair_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/eb7c1561-4531-5ef2-bf21-0649e16934f7
-- title:
--   Surjectivity of the glued Picard group onto the pair
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `HasPrincipalDivisors K F`: every nonzero $f \in F$ admits a finitely supported divisor $D : \mathrm{Place}\,K\,F \to_{f} \mathbb{Z}$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ and $\deg D = 0$, where a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and $\deg$ weights $v$ by its residue degree. Let $S$ be a finite set of ordered pairs of places. The group $\mathrm{GluedPic0}\,K\,F\,S$ is the quotient of the admissible gluing data — triples $(D_1, D_2, w)$ with $D_1, D_2$ divisors of degree $0$, $w : S \to \mathrm{Additive}\,K^\times$, and $D_1(s_1) = D_2(s_2) = 0$ for every $s = (s_1,s_2) \in S$ — by the subgroup of data satisfying `IsGluedPrincipal`, whose members in particular have $D_1 = \mathrm{div}(g_1)$ and $D_2 = \mathrm{div}(g_2)$ for nonzero $g_1, g_2 \in F$. The assertion is that the homomorphism `toPic0Pair S`, sending the class of $(D_1, D_2, w)$ to the pair of divisor classes $([D_1], [D_2])$ in $\mathrm{Pic}^0(F/K) \times \mathrm{Pic}^0(F/K)$, is surjective.
--
--   This is the statement that the generalised Jacobian attached to gluing the places of $S$ in pairs maps onto the product of two copies of the degree-zero divisor class group, the node data contributing only to the kernel. It is used in the comparison of torsion between $\mathrm{Pic}^0$ and the glued group, and in the divisibility statement [`AlgebraicCurve.GluedPic0.exists_nsmul_eq_of_forall_pic0`](thm.html#AlgebraicCurve.GluedPic0.exists_nsmul_eq_of_forall_pic0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_toPic0Pair_surjective.lean

import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.GluedPic0.toPic0Pair_surjective {K F : Type*} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F)) :
    Function.Surjective (AlgebraicCurve.GluedPic0.toPic0Pair S) := by sorry
