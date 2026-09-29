-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
-- name    : AlgebraicCurve.Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/dabf8636-b5ee-5e58-bedb-b6b4c094a26e
-- title:
--   Places of F/K over a Dedekind order are determined by their centre
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $A$ be a $K$-subalgebra of $F$ which is a Dedekind domain having $F$ as its field of fractions. Let $v$ and $v'$ be places of $F$ over $K$, that is, each consists of a valuation subring $\mathcal{O}_v \subseteq F$ (respectively $\mathcal{O}_{v'}$) containing the image of $K$ under the structure map, different from the whole of $F$, and whose ideals are all principal. Assume that each element of $A$, viewed in $F$, lies in $\mathcal{O}_v$ and also in $\mathcal{O}_{v'}$, so that both places contain the order $A$. Assume further that the two places have the same centre on $A$: for every $a \in A$, the image of $a$ in $F$ lies in the set of nonunits of $\mathcal{O}_v$ (the elements of valuation $< 1$, i.e. the maximal ideal) if and only if it lies in the set of nonunits of $\mathcal{O}_{v'}$. Then $v = v'$, i.e. the two places are equal as structures, their valuation subrings coinciding.
--
--   This is the standard uniqueness statement of valuation theory that a valuation ring of $F$ dominating a localisation of a Dedekind order $A$ with fraction field $F$ is determined by the prime of $A$ it cuts out. It is used in the project to reduce the identification of a place to the identification of its centre, and is cited in the analysis of intersections of places with prescribed maximal ideals and in the uniqueness of the moduli place on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.eq_of_forall_coe_mem_nonunits_iff_of_isDedekindDomain
    {K F : Type*} [Field K] [Field F] [Algebra K F] (A : Subalgebra K F)
    [IsDedekindDomain ↥A] [IsFractionRing ↥A F]
    (v v' : AlgebraicCurve.Place K F)
    (hv : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring) (hv' : ∀ a : ↥A, (a : F) ∈ v'.toValuationSubring)
    (h : ∀ a : ↥A, (a : F) ∈ v.toValuationSubring.nonunits ↔ (a : F) ∈ v'.toValuationSubring.nonunits) :
    v = v' := by sorry
