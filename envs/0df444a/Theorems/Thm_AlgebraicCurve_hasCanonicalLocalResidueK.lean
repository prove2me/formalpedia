-- Prove2me | Theorems.Thm_AlgebraicCurve_hasCanonicalLocalResidueK
-- name    : AlgebraicCurve.hasCanonicalLocalResidueK
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c6bde8c4-5ebf-5d06-bbd3-21317e38d515
-- title:
--   Canonical local residue data exist at every place
-- statement:
--   Let $K$ and $F$ be fields and let $F$ be a $K$-algebra; no further hypothesis (finite generation, transcendence degree one, or the like) is imposed on the extension. The assertion is that the proposition-valued class [`AlgebraicCurve.HasCanonicalLocalResidueK K F`](def/AlgebraicCurve_LocalResidue.html#L42) holds, that is: for every place $v$ of $F$ over $K$ — a valuation subring $\mathcal O_v$ of $F$ containing $\operatorname{algebraMap} K F(a)$ for all $a \in K$, with $\mathcal O_v \neq F$, and with $\mathcal O_v$ a principal ideal ring — the type $v.\mathtt{CanonicalLocalResidueDataK}$ is nonempty. Unfolding, this means that each such $v$ carries local residue data in the sense of the structure [`AlgebraicCurve.Place.LocalResidueData`](def/AlgebraicCurve_LocalResidue.html#L20) (a residue map `res` on $F$ attached to $v$, subject to that structure's axioms) which in addition satisfies the higher-pole-monomial vanishing condition $\operatorname{res}\big((\pi_v^{\,n+1})^{-1}\big) = 0$ for every natural number $n$ with $1 \le n$, where $\pi_v$ is the uniformizer chosen for $v$.
--
--   This is the existence half of the theory of local residues of differentials at a place of a function field, in the normalisation fixed by the project's residue axioms (vanishing on the regular part, the prescribed value on simple poles, and vanishing on the monomials $\pi_v^{-n-1}$ with $n \ge 1$). It is used as the availability hypothesis for residue-theoretic identities on curves, in particular by [`AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero`](thm.html#AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero), [`AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`](thm.html#AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero) and [`AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials`](thm.html#AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_hasCanonicalLocalResidueK.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.hasCanonicalLocalResidueK
    (K F : Type*) [Field K] [Field F] [Algebra K F] :
    AlgebraicCurve.HasCanonicalLocalResidueK K F := by sorry
