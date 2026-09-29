-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0f65dfe1-520c-59f1-8993-210ee85dd8a1
-- title:
--   Genus preservation under good reduction, via Riemann–Roch data
-- statement:
--   Let $L$ be an algebraically closed field, $F$ a field equipped with an $L$-algebra structure, and $f \in F$ an element such that $F$ is finite-dimensional and separable over the intermediate field $L(f) =$ `IntermediateField.adjoin L {f}`. Then there is a finite subset $S \subseteq L$, all of whose elements are nonzero, with the following property. Let $A$ be a valuation subring of $L$ whose valuation takes the value $1$ at every $s \in S$ (so each $s$ is a unit of $A$), let $Fb$ be a field with an algebra structure over the residue field $\kappa(A) =$ `IsLocalRing.ResidueField A`, and let $R$ be a regular prolongation of $A$ to $F$ with residue field $Fb$: that is, a valuation subring `R.integers` of $F$ together with a surjective ring homomorphism `R.residue` to $Fb$ whose kernel is the maximal ideal of `R.integers`, such that for $x \in L$ one has $x \in A$ exactly when $\mathrm{alg}(x) \in$ `R.integers`, such that `R.residue` is compatible with the residue map of $A$ over $\kappa(A) \to Fb$, and such that every nonzero $e \in F$ can be scaled by some $c \in L$ so that $c \cdot e$ lies in `R.integers` with nonzero residue. Assume $f \in$ `R.integers`, that the residue $\bar f =$ `R.residue` $f$ is transcendental over $\kappa(A)$, and that the fundamental equality $[Fb : \kappa(A)(\bar f)] = [F : L(f)]$ of finranks holds. Then for every integer $m$ there exist a divisor $D$ for $F/L$ and a divisor $\bar D$ for $Fb/\kappa(A)$ — finitely supported $\mathbb{Z}$-valued functions on the places, a place being a valuation subring containing the constants, distinct from the whole field and a principal ideal ring — such that $m \le \deg D$, $\deg \bar D = \deg D$ (degree being the sum of the coefficients weighted by the residue degrees of the places), and $\ell(\bar D) = \ell(D)$, where $\ell$ denotes the dimension over the constant field of the associated Riemann–Roch space.
--
--   This is Deuring's genus-preservation theorem for good reduction of a one-variable function field, stated through Riemann–Roch data rather than through the genus: outside a finite set of exceptional constants, divisors of arbitrarily large equal degree upstairs and downstairs have equal $\ell$, which by Riemann–Roch in degrees above $2g-2$ forces the two genera to agree. It feeds into [`AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_and_forall_residueField_pow_pow_eq_self), where a reduction of a curve with controlled residue fields is produced; the inequality half of the comparison is supplied by [`AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le`](thm.html#AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∀ m : ℤ, ∃ (D : AlgebraicCurve.Divisor L F) (Db : AlgebraicCurve.Divisor (IsLocalRing.ResidueField A) Fb),
            m ≤ AlgebraicCurve.Divisor.degree D ∧
              AlgebraicCurve.Divisor.degree Db = AlgebraicCurve.Divisor.degree D ∧
                AlgebraicCurve.ell Db = AlgebraicCurve.ell D := by sorry
