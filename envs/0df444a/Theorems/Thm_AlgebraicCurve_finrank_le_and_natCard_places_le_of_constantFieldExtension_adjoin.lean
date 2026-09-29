-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
-- name    : AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/a93a0fd6-b762-5620-a1c2-4211647c1f99
-- title:
--   Constant field extension: degree and zero/pole counts
-- statement:
--   Let $k$ be an algebraically closed field of characteristic $0$ and let $F$ be a field extension of $k$ which is a curve over $k$ in the sense of the project's predicate [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place equals $\operatorname{ord}_P(f)$, every place $P$ of $F$ over $k$ (a valuation subring of $F$ containing the image of $k$, different from $F$ itself, and a principal ideal ring) has residue field finite-dimensional over $k$, and $\Omega[F/k]$ is free of rank one over $F$. Let $y \in F$ be transcendental over $k$ with $F$ finite-dimensional over $k(y) =$ `IntermediateField.adjoin k {y}`. Let $K'$ be a field extension of $k$, let $L$ be a field extension of $K'$, let $t \in L$ be transcendental over $K'$, and let $E$ be an intermediate field between $K'(t)$ and $L$ with $E$ finite-dimensional over $K'(t)$. Assume $E$ is an $F$-algebra and a $k$-algebra compatibly with the towers $k \subseteq K' \subseteq E$ and $k \subseteq F \subseteq E$, that the image of $y$ in $E$ equals $t$ in $L$, and that $E$ is generated over $K'$ by the image of $F$. Then $[F : k(y)] \le [E : K'(t)]$, and for every nonzero $u \in F$ the set of places $P$ of $E$ over $K'$ with $\operatorname{ord}_P(\varphi(u)) > 0$ is finite of cardinality at most the number of places of $F$ over $k$ at which $u$ has positive order, and likewise the set of places of $E$ over $K'$ with $\operatorname{ord}_P(\varphi(u)) < 0$ is finite of cardinality at most the number of places of $F$ over $k$ at which $u$ has negative order, where $\varphi$ denotes the structure map $F \to E$ and $\operatorname{ord}$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This is the comparison of a one-variable function field with its constant field extension, realised concretely inside a finite extension of $K'(t)$: the degree over the rational subfield does not drop and the numbers of zeros and of poles of a function do not increase. It is used in the counting arguments for modular curves, where fibres of a map of curves are matched with double cosets ([`ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index`](thm.html#ModularCurve.natCard_doubleCoset_le_card_fibres_of_finrank_eq_index), [`ModularCurve.natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index`](thm.html#ModularCurve.natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index), [`ModularCurve.natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset`](thm.html#ModularCurve.natCard_place_ord_neg_laurentBaseChange_gamma1_eq_natCard_doubleCoset)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped IntermediateField

theorem AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {F : Type*} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (y : F) (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set F)) F]
    {K' : Type*} [Field K'] [Algebra k K']
    {L : Type*} [Field L] [Algebra K' L] (t : L) (ht : Transcendental K' t)
    (E : IntermediateField (IntermediateField.adjoin K' ({t} : Set L)) L)
    [FiniteDimensional (IntermediateField.adjoin K' ({t} : Set L)) E]
    [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]
    (hyt : (algebraMap F E y : L) = t)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤) :
    Module.finrank (IntermediateField.adjoin k ({y} : Set F)) F ≤
        Module.finrank (IntermediateField.adjoin K' ({t} : Set L)) E ∧
      ∀ u : F, u ≠ 0 →
        (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
            Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
        (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
            Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by sorry
