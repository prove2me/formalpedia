-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
-- name    : AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a52b3862-44d2-5e32-aaff-95c3540afd01
-- title:
--   Deuring's reduction of div(f) at a finite place
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k = \mathrm{ResidueField}\,A$, and let $F/L$ and $\bar F/k$ be fields satisfying `IsCurveOver` (principal divisors exist, all places have residue fields finite over the base, and the module of Kähler differentials is free of rank one). Let $R$ be a regular prolongation of $A$ to $F$ with reduction $\bar F$: a valuation subring $\mathcal O = R.integers \subseteq F$ with $\mathcal O \cap L = A$, together with a surjective ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$ whose kernel is the maximal ideal of $\mathcal O$ and which is compatible with $A \to k$, such that every nonzero element of $F$ has an $L$-multiple lying in $\mathcal O$ with nonzero residue. Let $x \in \mathcal O$ have residue $\bar x$ transcendental over $k$, assume $0 < [\bar F : k(\bar x)]$ and $[F : L(x)] = [\bar F : k(\bar x)]$, and assume the chart hypothesis that every $h \in \bar F$ integral over $k[\bar x]$ equals $\bar g$ for some $g \in \mathcal O$ integral over $L[x]$. Let $f \in \mathcal O$ with $\bar f \neq 0$, let $Q$ be a place of $\bar F/k$ whose valuation subring contains $\bar x$, let $D$ be a divisor of $F/L$ (a finitely supported integer-valued function on places) with $D(P) = \mathrm{ord}_P(f)$ for every place $P$, and let $T$ be a finite set of places of $F/L$ consisting exactly of those $P$ such that $D(P) \neq 0$, such that $x - a$ lies in the maximal ideal of $\mathcal O_P$ for some $a \in A$, and such that for every $h \in \mathcal O$ integral over $L[x]$ and every $a \in A$ with $h - a$ in the maximal ideal of $\mathcal O_P$ one has $\bar h - \bar a$ in the maximal ideal of $\mathcal O_Q$. Then $\sum_{P \in T} D(P) = \mathrm{ord}_Q(\bar f)$, where $\mathrm{ord}$ is minus the logarithm of the associated adic valuation.
--
--   This is Deuring's multiplicity formula for the reduction of the divisor of a unit of $\mathcal O$, read off at a single place $Q$ of the affine chart determined by $x$: the orders at all places of $F/L$ lying in that chart and reducing to $Q$ add up to the order of $\bar f$ at $Q$ (zeros and poles reducing to the same $Q$ may cancel). Together with the existence and uniqueness of the reduced place it is used to construct the reduction map on places and to prove that it pushes forward principal divisors to principal divisors, which in turn feeds the divisor laws for fibre models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by sorry
