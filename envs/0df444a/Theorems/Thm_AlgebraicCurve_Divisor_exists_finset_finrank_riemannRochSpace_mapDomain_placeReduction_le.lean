-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
-- name    : AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d471cac9-31a5-544f-95b3-5853532171f9
-- title:
--   Generic upper bound for constant reduction of divisors
-- statement:
--   Let $K$, $F$, $E$, $FE$ be fields with $K$-algebra structures on $F$, $E$, $FE$, an $E$-algebra structure on $FE$ and an $F$-algebra structure on $FE$, compatible as scalar towers $K \subseteq E \subseteq FE$ and $K \subseteq F \subseteq FE$, with $K$ algebraically closed of characteristic $0$ and $E$ algebraically closed. Assume $F$ contains an element transcendental over $K$ over whose generated subfield $F$ is finite, and likewise for $FE$ over $E$; assume `IsCurveOver K F` and `IsCurveOver E FE` (existence of principal divisors of degree $0$ realising the orders $v.\mathrm{ord}\,f$, finite residue extensions at every place, and $\Omega_{F/K}$, resp. $\Omega_{FE/E}$, free of rank one); and assume $FE$ is generated over $E$ by the image of $F$. Let $D$ be a divisor of $FE/E$, i.e. a finitely supported $\mathbb{Z}$-valued function on places of $FE/E$, a place being a proper valuation subring containing the base field and being a principal ideal ring. Then there is a finite set $S \subseteq E$ with $0 \notin S$ such that: for every valuation subring $A \subseteq E$ and every map $r$ from places of $FE/E$ to places of $F/K$, if $A$ contains the image of $K$, every $a \in A$ satisfies $\mathrm{val}_A(a - k) < 1$ for some $k \in K$, every $s \in S$ satisfies $\mathrm{val}_A(s) = 1$, and $r$ is given by Deuring reduction along $A$, namely $f \in F$ lies in the valuation subring of $r(P)$ exactly when $\mathrm{val}_P(f - a) < 1$ for some $a \in A$, then $\dim_K$ of the Riemann–Roch space $\{f \in F : v(f) \le \exp(D'(v))\ \text{for all places } v\}$ of the pushforward divisor $D' =$ `Finsupp.mapDomain r D` is at most $\dim_E$ of the corresponding space for $D$.
--
--   This is the generic half of Deuring's theorem on the behaviour of the dimension of a divisor under constant reduction: the inequality $\ell_K(r_*D) \le \ell_E(D)$ holds for all reductions along valuation subrings of $E$ with residue field $K$ that leave a finite set of elements attached to $D$ invertible, the reverse inequality being available unconditionally. It feeds the companion statement [`AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq`](thm.html#AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq), where the two inequalities are combined into an equality of dimensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) :
    ∃ S : Finset E, (0 : E) ∉ S ∧
      ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
        (∀ k : K, algebraMap K E k ∈ A) →
        (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
        (∀ s ∈ S, A.valuation s = 1) →
        (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
          ∃ a : E, a ∈ A ∧
            P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
        Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) ≤
          Module.finrank E (riemannRochSpace D) := by sorry
