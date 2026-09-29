-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq
-- name    : AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/7255dc9b-d9f6-531a-b34b-7d69d4b4c08f
-- title:
--   Deuring–Roquette: invariance of ℓ(D) under good constant reduction
-- statement:
--   Let $K \subseteq E$ and $F \subseteq FE$ be fields arranged in a commutative square of algebras with $K$ at the bottom and $FE$ at the top (both towers $K \to E \to FE$ and $K \to F \to FE$ being scalar towers), with $K$ and $E$ algebraically closed and $K$ of characteristic $0$. Assume $F$ contains an element $x$ transcendental over $K$ with $F$ finite over $K(x)$, and likewise $FE$ contains an element transcendental over $E$ with $FE$ finite over the subfield it generates; assume the predicates `IsCurveOver K F` and `IsCurveOver E FE`, i.e. on each level every nonzero element has a degree-zero divisor of its orders at all places, every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank $1$ over the function field; and assume $FE$ is generated over $E$ by the image of $F$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Then for every divisor $D$ of $FE$ over $E$ there is a finite set $S \subseteq E$ with $0 \notin S$ such that the following holds for every valuation subring $A$ of $E$ and every map $r$ from places of $FE/E$ to places of $F/K$: if $A$ contains the image of $K$, if every $a \in A$ satisfies $A$-valuation $(a - \lambda) < 1$ for some $\lambda$ in the image of $K$ (residue field $K$), if every $s \in S$ is a unit of $A$ (i.e. has $A$-valuation $1$), and if $r$ is the Deuring reduction along $A$, meaning that for each place $P$ of $FE/E$ and each $f \in F$ one has $f$ in the valuation subring of $r(P)$ exactly when the $P$-valuation of $f - a$ is $< 1$ for some $a \in A$, then $$\dim_K L\bigl(r_*D\bigr) = \dim_E L(D),$$ where $r_*D$ is the pushforward `Finsupp.mapDomain r D` and $L(D)$ denotes the $\{f : v(f) \le \exp(D v)$ for all places $v\}$ Riemann–Roch space.
--
--   This is Deuring's theorem, in the refinement due to Roquette, that the dimension of a divisor on a curve over $E$ is unchanged by all sufficiently good $K$-rational constant reductions, the finitely many excluded reductions being controlled by the auxiliary finite set $S$ attached to $D$. It is used to transfer principality of divisors between $FE/E$ and $F/K$, in the form cited by [`AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction`](thm.html#AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq
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
        Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) =
          Module.finrank E (riemannRochSpace D) := by sorry
