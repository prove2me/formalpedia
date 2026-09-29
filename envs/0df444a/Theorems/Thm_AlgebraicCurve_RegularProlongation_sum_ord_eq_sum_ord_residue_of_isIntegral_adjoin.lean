-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
-- name    : AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/42995e83-7a8c-51d0-8804-90e6c955f3f2
-- title:
--   Deuring reduction: equal multiplicity totals on the finite chart
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k$, and let $F/L$ and $\bar F/k$ both satisfy `IsCurveOver` (principal divisors exist for every nonzero element, every place has residue field finite over the base, and the module of Kähler differentials is free of rank one). Let $R$ be a regular prolongation of $A$ to $F$ with reduction $\bar F$: a valuation subring $\mathcal O =$ `R.integers` of $F$ with $\mathcal O \cap L = A$, a surjective ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$ whose kernel is the maximal ideal of $\mathcal O$ and which is compatible with $A \to k$, such that every nonzero element of $F$ has an $L$-multiple lying in $\mathcal O$ with nonzero residue. Let $x \in \mathcal O$ have $\bar x = \mathrm{res}\,x$ transcendental over $k$, with $[\bar F : k(\bar x)]$ positive and equal to $[F : L(x)]$, and assume every $h \in \bar F$ integral over $k[\bar x]$ is $\mathrm{res}\,f$ for some $f \in \mathcal O$ integral over $L[x]$. Let $f \in \mathcal O$ be integral over $L[x]$ with $\mathrm{res}\,f \neq 0$; let $D$ be a divisor of $F/L$ with $D(P) = \mathrm{ord}_P f$ at every place, and $\bar D$ a divisor of $\bar F/k$ with $\bar D(Q) = \mathrm{ord}_Q(\mathrm{res}\,f)$. Let $T_P$ be the finite set of places $P$ of $F/L$ with $D(P) \neq 0$ for which $x - a$ lies in the maximal ideal of the valuation subring of $P$ for some $a \in A$, and $T_Q$ the finite set of places $Q$ of $\bar F/k$ with $\bar D(Q) \neq 0$ and $\bar x$ in the valuation subring of $Q$. Then $\sum_{P \in T_P} D(P) = \sum_{Q \in T_Q} \bar D(Q)$.
--
--   This is the global counting half of Deuring's multiplicity formula for the reduction of a one-variable function field along a valuation of the constant field, restricted to elements of $\mathcal O$ integral over $L[x]$: the total order of $f$ over the places of the finite chart $x \in A$ equals the total order of $\mathrm{res}\,f$ over the places where $\bar x$ is finite. Combined with the local inequality [`AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin`](thm.html#AlgebraicCurve.RegularProlongation.ord_residue_le_sum_ord_of_isIntegral_adjoin) and the existence and uniqueness of the reduced place, it yields the place-by-place formula [`AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective`](thm.html#AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin
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
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (Dbar : Divisor (IsLocalRing.ResidueField A) Fbar)
    (hDbar : ∀ Q, Dbar Q = Q.ord (R.residue f))
    (TP : Finset (Place L F))
    (hTP : ∀ P, P ∈ TP ↔ (D P ≠ 0 ∧
      ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits))
    (TQ : Finset (Place (IsLocalRing.ResidueField A) Fbar))
    (hTQ : ∀ Q, Q ∈ TQ ↔ (Dbar Q ≠ 0 ∧ R.residue x ∈ Q.toValuationSubring)) :
    ∑ P ∈ TP, D P = ∑ Q ∈ TQ, Dbar Q := by sorry
