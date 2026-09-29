-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
-- name    : AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/25bc8b6c-ca1a-5e83-85a7-d96b0567defe
-- title:
--   Semicontinuity of divisor dimension under constant reduction
-- statement:
--   Let $K$, $F$, $E$, $FE$ be fields with $K$-algebra structures on $F$, $E$, $FE$ and $E$- and $F$-algebra structures on $FE$ forming scalar towers $K \subseteq E \subseteq FE$ and $K \subseteq F \subseteq FE$, with $K$ algebraically closed of characteristic $0$ and $E$ algebraically closed. Assume $F$ contains an element transcendental over $K$ over whose adjunction $F$ is finite-dimensional, and likewise $FE$ over $E$; assume `IsCurveOver K F` and `IsCurveOver E FE`, i.e. in each case every nonzero function has a degree-zero divisor recording its orders at all places, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank $1$; and assume $FE$ is generated over $E$ by the image of $F$. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $D$ be a divisor of $FE/E$, let $A$ be a valuation subring of $E$ containing the image of $K$ and such that every $a \in A$ satisfies $A$-valuation of $a - \operatorname{algebraMap} k < 1$ for some $k \in K$, and let $r$ be a map from places of $FE/E$ to places of $F/K$ such that for every place $P$ and every $f \in F$, $f$ lies in the valuation subring of $r(P)$ precisely when the $P$-valuation of $f - a$ (images taken in $FE$) is $< 1$ for some $a \in A$. Then the $E$-dimension of the space of $f \in FE$ with $P$-adic valuation at most $\exp(D\,P)$ at every place $P$ of $FE/E$ is at most the $K$-dimension of the corresponding space for the divisor `Finsupp.mapDomain r D` of $F/K$, whose value at a place $v$ is the sum of the values of $D$ over the fibre of $r$ above $v$.
--
--   This is Deuring's lower semicontinuity of the dimension of a divisor under constant reduction, here in the situation of a constant-field extension $FE = F\cdot E$ and a $K$-rational valuation subring $A \subseteq E$, with $r$ the induced reduction map on places. It is used by [`AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq`](thm.html#AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq), where the reverse comparison is obtained for suitable divisors and the two dimensions are matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE)
    (A : ValuationSubring E) (r : Place E FE → Place K F)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) :
    Module.finrank E (riemannRochSpace D) ≤
      Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) := by sorry
