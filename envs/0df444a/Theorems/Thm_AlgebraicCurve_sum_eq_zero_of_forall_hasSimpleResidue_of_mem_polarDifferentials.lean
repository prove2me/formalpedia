-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
-- name    : AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/44f5a462-4b88-51b6-8916-240500d34fbe
-- title:
--   Residue theorem for differentials with at most simple poles
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field which is a $K$-algebra, essentially of finite type over $K$, and which is a curve over $K$ in the sense of the project: every nonzero $f \in F$ has a finitely supported divisor of degree zero recording the orders $\mathrm{ord}_v(f)$, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; assume moreover that $F$ has a canonical divisor, i.e. every nonzero $\omega \in \Omega_{F/K}$ admits a finitely supported divisor whose value at each place $v$ is $\mathrm{ord}_v$ of the differential coefficient of $\omega$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring; each place $v$ carries a chosen uniformiser $\pi_v$ and the differential $d\pi_v$. Let $S$ be a finite set of places and let $\omega$ lie in the $K$-submodule of polar differentials for $S$: for every place $v \notin S$ one has $\omega = f \cdot d\pi_v$ with $f$ in the valuation ring $\mathcal{O}_v$, and for every $v \in S$ one has $\omega = f \cdot d\pi_v$ with $\pi_v f \in \mathcal{O}_v$. Let $a$ be a $K$-valued function on places such that for each $v \in S$ there is $f \in F$ with $\omega = f \cdot d\pi_v$, $\pi_v f \in \mathcal{O}_v$ and residue of $\pi_v f$ in the residue field of $v$ equal to the image of $a(v)$. Then $\sum_{v \in S} a(v) = 0$. The values of $a$ outside $S$ are unconstrained.
--
--   This is the residue theorem $\sum_v \mathrm{res}_v(\omega) = 0$ for a differential on a curve over an algebraically closed field whose poles are simple and confined to a finite set $S$, phrased in terms of residues read off from $\omega = f\,d\pi_v$. It is used in the construction of the linear map sending a polar differential to its tuple of residues, in the converse statement that any residue tuple summing to zero is realised, and in the analysis of differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (ω : Ω[F⁄K])
    (hω : ω ∈ AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F)))
    (a : AlgebraicCurve.Place K F → K) (ha : ∀ v ∈ S, v.HasSimpleResidue ω (a v)) :
    ∑ v ∈ S, a v = 0 := by sorry
