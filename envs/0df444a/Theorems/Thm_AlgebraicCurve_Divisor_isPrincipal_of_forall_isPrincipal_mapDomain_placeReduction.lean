-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
-- name    : AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/33fef07c-b1e8-5296-911a-a5ee266d06c2
-- title:
--   Specialisation principle for principal divisors under constant reduction
-- statement:
--   Let $K\subseteq E$ be algebraically closed fields with $K$ of characteristic $0$, and let $F/K$ and $FE/E$ be fields fitting into a commutative tower of $K$-algebras $K\to E\to FE$, $K\to F\to FE$. Assume $F$ contains an element transcendental over $K$ over whose generated subfield $F$ is finite-dimensional, and likewise $FE$ over $E$; assume further `IsCurveOver K F` and `IsCurveOver E FE`, i.e. for each of the two extensions every nonzero function has a divisor of degree $0$, every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank $1$ over the function field; and assume $FE$ is generated over $E$ by the image of $F$ (`hgen`). Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring, and a divisor is a finitely supported $\mathbb Z$-valued function on places. Let $D$ be a divisor of $FE/E$ of degree $0$ (the weighted sum $\sum_P D(P)\cdot\deg P$ vanishes). Suppose that for every valuation subring $A\subseteq E$ and every map $r$ from places of $FE/E$ to places of $F/K$ such that $A$ contains the image of $K$, every $a\in A$ satisfies $\mathrm{val}_A(a-k)<1$ for some $k\in K$, and for all places $P$ of $FE/E$ and all $f\in F$ one has $f\in\mathcal O_{r(P)}$ if and only if $\mathrm{val}_P(f-a)<1$ for some $a\in A$, the pushforward divisor `Finsupp.mapDomain r D` is principal on $F/K$, that is, equals $v\mapsto \mathrm{ord}_v(g)$ for some $g\in F^{\times}$. Then $D$ itself is principal: there is $h\in FE$, $h\neq 0$, with $D(P)=\mathrm{ord}_P(h)$ for every place $P$ of $FE/E$.
--
--   This is the specialisation principle for linear equivalence on a curve with constant field extension: a degree-zero divisor class on the base change to $E$ all of whose Deuring reductions along $K$-rational places of the constants vanish is itself zero. It is used in the treatment of correspondences and of the degree-zero part of the divisor class group, where it is cited by [`AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero); the proof invokes the existence of a valuation subring of $E$ with residue retraction to $K$ avoiding a prescribed finite set, the comparison of Riemann–Roch spaces under reduction of places, and the construction of places from valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) (hD : D.degree = 0)
    (h : ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
      (∀ k : K, algebraMap K E k ∈ A) →
      (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
      (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
        ∃ a : E, a ∈ A ∧
          P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
      Divisor.IsPrincipal (K := K) (F := F) (Finsupp.mapDomain r D)) :
    D.IsPrincipal := by sorry
