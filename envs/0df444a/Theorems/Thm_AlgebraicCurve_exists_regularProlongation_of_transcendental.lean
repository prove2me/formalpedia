-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_regularProlongation_of_transcendental
-- name    : AlgebraicCurve.exists_regularProlongation_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2bea79e0-16dd-52c9-be0d-efea0d156de9
-- title:
--   Existence of a regular prolongation with residually transcendental f
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with residue field $\mathrm{ResidueField}\,A$. Let $F$ be a field extension of $L$, let $f \in F$ be transcendental over $L$, and assume $F$ is algebraic over the intermediate field $L(f)$ obtained by adjoining $f$ to $L$ inside $F$. The conclusion asserts the existence of a valuation subring $W$ of $F$, of an algebra structure on the residue field of $W$ over the residue field of $A$, and of a term $R$ of the structure `RegularProlongation A F (IsLocalRing.ResidueField W)`, that is, of a valuation subring $R.\mathrm{integers}$ of $F$ together with a ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \mathrm{ResidueField}\,W$ such that: for $x \in L$ one has $x \in A$ if and only if its image in $F$ lies in $R.\mathrm{integers}$; $R.\mathrm{residue}$ is surjective with kernel the maximal ideal of $R.\mathrm{integers}$; on elements of $A$ it agrees with the residue map $A \to \mathrm{ResidueField}\,A$ followed by the given algebra map to $\mathrm{ResidueField}\,W$; and every nonzero $g \in F$ admits $c \in L$ with $c \cdot g \in R.\mathrm{integers}$ and $R.\mathrm{residue}(c \cdot g) \neq 0$. Moreover $R.\mathrm{integers} = W$, and $f$ lies in $R.\mathrm{integers}$ with $R.\mathrm{residue}(f)$ transcendental over $\mathrm{ResidueField}\,A$.
--
--   This is the existence statement for Deuring's reduction of a one-variable function field with respect to a place of its constant field: a valuation of $L$ extends to $F$ without raising the ramification index, with residue field generated over the residue field of $A$ by a transcendental reduction of the chosen non-constant element $f$. It is obtained from the corresponding statement for the rational function field `RatFunc L`, and is used in [`AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder`](thm.html#AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder) to produce good constant reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_regularProlongation_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_regularProlongation_of_transcendental
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) (htrL : Transcendental L f)
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ (W : ValuationSubring F)
      (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R.integers = W ∧ ∃ hfR : f ∈ R.integers,
        Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) := by sorry
