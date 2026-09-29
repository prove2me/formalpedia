-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin
-- name    : AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/353e6048-d6d8-5467-b82f-35f3b5da7149
-- title:
--   Deuring's multiplicity inequality on the finite chart
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with residue field $k = \mathrm{ResidueField}\,A$. Let $F$ be a field extension of $L$ and $\bar F$ a field extension of $k$, both one-variable function fields in the sense of `IsCurveOver` (every nonzero element has a degree-zero principal divisor whose value at each place is the normalised order of the element there, every place has residue field finite over the base, and the module of Kähler differentials is free of rank one). Let $R$ be a regular prolongation of $A$ to $F$ with reduction $\bar F$: a valuation subring $R.\mathrm{integers} \subseteq F$ meeting $L$ exactly in $A$, together with a surjective ring homomorphism $R.\mathrm{residue}$ to $\bar F$ whose kernel is the maximal ideal, compatible with $A \to k$, and such that every nonzero element of $F$ has a scalar multiple lying in $R.\mathrm{integers}$ with nonzero residue. Let $x \in R.\mathrm{integers}$ have residue $\bar x$ transcendental over $k$, assume $0 < [\bar F : k(\bar x)]$ and $[F : L(x)] = [\bar F : k(\bar x)]$, and assume the chart hypothesis that every element of $\bar F$ integral over $k[\bar x]$ is the residue of some element of $R.\mathrm{integers}$ integral over $L[x]$. Let $f \in R.\mathrm{integers}$ be integral over $L[x]$ with $\bar f \neq 0$, let $Q$ be a place of $\bar F/k$ with $\bar x$ in its valuation ring, let $D$ be a divisor of $F/L$ with $D(P) = \mathrm{ord}_P(f)$ for every place $P$, and let $T$ be a finite set of places of $F/L$ consisting exactly of those $P$ with $D(P) \neq 0$ for which $x - a$ lies in the nonunits of $P$ for some $a \in A$, and for which every $h \in R.\mathrm{integers}$ integral over $L[x]$ and every $a \in A$ with $h - a$ in the nonunits of $P$ satisfy $\bar h - \bar a$ in the nonunits of $Q$. Then $\mathrm{ord}_Q(\bar f) \le \sum_{P \in T} D(P)$.
--
--   This is one inequality in Deuring's multiplicity formula $\sum_{P \rightsquigarrow Q} \mathrm{ord}_P(f) = \mathrm{ord}_Q(\bar f)$ for the reduction of a function field along a valuation of its constant field, here in the affine chart determined by $x$ and for elements integral over $L[x]$. It feeds into [`AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective`](thm.html#AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective) and [`AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin`](thm.html#AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin), where the corresponding equality is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin
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
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    Q.ord (R.residue f) ≤ ∑ P ∈ T, D P := by sorry
