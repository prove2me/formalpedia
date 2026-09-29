-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image
-- name    : AlgebraicCurve.RegularProlongation.exists_place_eq_of_residue_image
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/10bea4b4-4bbe-5971-b9f2-60879a672d30
-- title:
--   Reduction of a local subring as a rational place
-- statement:
--   Let $L$ and $F$ be fields with $F$ an $L$-algebra, let $A$ be a valuation subring of $L$, and let $\bar F$ be a field equipped with an algebra structure over the residue field $\kappa = \mathrm{ResidueField}\,A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ together with a ring homomorphism $R.\mathrm{residue}$ to $\bar F$ such that $\mathrm{algebraMap}\,L\,F\,x$ lies in $R.\mathrm{integers}$ exactly when $x \in A$, the residue map is surjective with kernel the maximal ideal of $R.\mathrm{integers}$, it restricts on $A$ to the structure map $\kappa \to \bar F$ composed with reduction, and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f$ integral and of nonzero residue. Let $S$ be a subring of $F$ which is a local ring, contained in $R.\mathrm{integers}$ (hypothesis `hSR`) and containing the image of $A$ under $\mathrm{algebraMap}\,L\,F$ (hypothesis `hAS`). Let $O$ be a valuation subring of $\bar F$ with $O \neq \top$, $O$ a principal ideal ring, and assume: $g \in O$ if and only if $g$ is the $R$-residue of an element of $S$; an element of $S$ lies in the maximal ideal of $S$ if and only if its residue is a non-unit of $O$; and every element of $S$ is congruent modulo the maximal ideal of $S$ to the image of some element of $A$. Then there is a place $Q$ of $\bar F$ over $\kappa$ — that is, a valuation subring of $\bar F$ containing the image of $\kappa$, distinct from $\top$, and a principal ideal ring — such that: its valuation subring is $O$; $Q$ is rational, i.e. $\kappa \to Q.\mathrm{ResidueField}$ is surjective; each $f \in S$ lies in $R.\mathrm{integers}$ with residue in $Q$'s valuation subring; conversely each element of that valuation subring is the residue of an element of $R.\mathrm{integers}$ lying in $S$; for $f \in S$ integral, $f$ is a unit of $S$ if and only if $Q.\mathrm{ord}$ of its residue is $0$ and that residue is nonzero; some $T \in S$ has residue of $Q.\mathrm{ord}$ equal to $1$; and any place $Q'$ of $\bar F$ over $\kappa$ whose valuation subring contains all residues of elements of $S$ equals $Q$.
--
--   This is the valuation-theoretic core of the construction of the place of reduction: a discrete (principal) proper valuation subring of $\bar F$ arising as the reduction of a local subring $S \subseteq R.\mathrm{integers}$ is the valuation ring of a unique place of $\bar F$ over the residue field of $A$, that place being rational, read off $S$ by the prolongation's residue map, detecting the units of $S$ by order zero, and admitting a uniformiser coming from $S$. It is the conclusion block used by [`AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus`](thm.html#AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus), where $S$ is a stalk at a smooth closed point of a relative curve and $O$ the corresponding fibre stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_place_eq_of_residue_image
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)

    (O : ValuationSubring Fbar) (hOtop : O ≠ ⊤) (hOpir : IsPrincipalIdealRing ↥O)
    (hO : ∀ g : Fbar, g ∈ O ↔ ∃ f : ↥S, R.residue ⟨(f : F), hSR f⟩ = g)

    (hloc : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ R.residue ⟨(f : F), hSR f⟩ ∈ O.nonunits)

    (hrat : ∀ f : ↥S, ∃ a : ↥A, f - ⟨algebraMap L F (a : L), hAS a⟩ ∈ maximalIdeal ↥S) :
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.toValuationSubring = O ∧
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ R.integers), f ∈ S ∧ R.residue ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ R.integers), Q.ord (R.residue ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by sorry
