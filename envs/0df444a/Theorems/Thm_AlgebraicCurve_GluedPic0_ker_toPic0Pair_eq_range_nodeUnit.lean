-- Prove2me | Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
-- name    : AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/dd89c1a7-5433-57a1-8ae0-208623a5e575
-- title:
--   Middle exactness of glued Pic⁰ at rational glued places
-- statement:
--   Let $F$ and $K$ be fields with $F$ a $K$-algebra, and let $S$ be a finite set of ordered pairs $(v_1,v_2)$ of places of $F/K$, a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$ and is a principal ideal ring. Assume that every place occurring in $S$ is $K$-rational in the sense that for each $s\in S$ the structure maps $K\to\kappa(s_1)$ and $K\to\kappa(s_2)$ to the residue fields of the two valuation subrings are surjective. Consider the group of gluing data $\mathrm{Div}(F/K)\times\mathrm{Div}(F/K)\times(S\to\mathrm{Additive}\,K^\times)$, its subgroup of admissible data (both divisors of degree zero, the first supported away from all first members $s_1$ and the second away from all second members $s_2$), and the quotient $\mathrm{GluedPic}^0_S$ of the admissible data by those admissible data satisfying `IsGluedPrincipal`, namely those for which there are nonzero $g_1,g_2\in F$ whose divisors are the two divisor components and units $a_s,b_s\in K^\times$ such that $g_1$ has value $a_s$ at $s_1$, $g_2$ has value $b_s$ at $s_2$, and the unit component is $s\mapsto a_s/b_s$. Then the kernel of the homomorphism $\mathrm{GluedPic}^0_S\to\mathrm{Pic}^0(F/K)\times\mathrm{Pic}^0(F/K)$ induced by forgetting the unit component equals the image of the homomorphism sending $w\colon S\to\mathrm{Additive}\,K^\times$ to the class of $(0,0,w)$.
--
--   This is the exactness at the middle term of the sequence $(S\to K^\times)\to\mathrm{GluedPic}^0_S\to\mathrm{Pic}^0\times\mathrm{Pic}^0$, which exhibits the degree-zero Picard group of a curve obtained by gluing two branches at the ordinary double points indexed by $S$ as an extension of the Picard groups of the normalisation by a torus of node units. It is used in the further analysis of $\mathrm{GluedPic}^0_S$, for instance in the results on divisibility and on torsion elements killed by a power of the characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit.lean

import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).2.ResidueField))) :
    (AlgebraicCurve.GluedPic0.toPic0Pair S).ker = (AlgebraicCurve.GluedPic0.nodeUnit S).range := by sorry
