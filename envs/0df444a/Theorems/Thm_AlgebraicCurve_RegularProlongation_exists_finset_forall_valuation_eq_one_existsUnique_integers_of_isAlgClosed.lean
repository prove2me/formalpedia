-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
-- name    : AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e69168ff-3049-5009-bbb5-8784a8f083d3
-- title:
--   Deuring's good-place lemma for regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field and $F$ a field extension of $L$, and let $f \in F$ be transcendental over $L$ with $F$ finite-dimensional and separable over the intermediate field $L(f) =$ `IntermediateField.adjoin L {f}`. The assertion is that there is a finite subset $S \subseteq L$ all of whose elements are nonzero, such that for every valuation subring $A$ of $L$ whose associated valuation takes the value $1$ at every $s \in S$ (that is, every element of $S$ is a unit of $A$) the following holds. Writing $\kappa =$ `IsLocalRing.ResidueField A`, there exist a field $\bar F$ (in the universe of $F$), a $\kappa$-algebra structure on $\bar F$, and a regular prolongation $R$ of $A$ to $F$ with residue target $\bar F$ — i.e. a valuation subring $R.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ whose kernel is the maximal ideal of $R.\mathrm{integers}$, such that for $x \in L$ one has $x \in A$ iff the image of $x$ in $F$ lies in $R.\mathrm{integers}$, the square with $\kappa \to \bar F$ and the residue map of $A$ commutes, and every nonzero $e \in F$ admits $c \in L$ with $c \cdot e \in R.\mathrm{integers}$ and $R.\mathrm{residue}(c \cdot e) \neq 0$ — such that $f \in R.\mathrm{integers}$, the residue $\bar f = R.\mathrm{residue}\, f$ is transcendental over $\kappa$, the degree equality $[\bar F : \kappa(\bar f)] = [F : L(f)]$ of `Module.finrank`s holds, and, for every field $\bar F'$ with a $\kappa$-algebra structure and every regular prolongation $R'$ of $A$ to $F$ with residue target $\bar F'$ such that $f \in R'.\mathrm{integers}$ and $R'.\mathrm{residue}\, f$ is transcendental over $\kappa$, one has $R'.\mathrm{integers} = R.\mathrm{integers}$. Thus the uniqueness asserted is uniqueness of the valuation subring of $F$, not of the prolongation datum.
--
--   This is Deuring's good-place lemma: away from a finite set of places of the algebraically closed constant field, a one-variable function field $F/L$ presented by a separating element $f$ admits a regular prolongation in which $f$ stays integral with transcendental residue, the fundamental degree equality is preserved, and the underlying valuation subring of $F$ is determined. It is used in the construction of a good constant reduction in [`AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v

theorem AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∃ (Fb : Type v) (_ : Field Fb) (_ : Algebra (IsLocalRing.ResidueField A) Fb)
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) ∧
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ∧
          ∀ (Fb' : Type v) [Field Fb'] [Algebra (IsLocalRing.ResidueField A) Fb']
            (R' : AlgebraicCurve.RegularProlongation A F Fb') (hfR' : f ∈ R'.integers),
            Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hfR'⟩) →
              R'.integers = R.integers := by sorry
