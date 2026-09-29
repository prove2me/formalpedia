-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
-- name    : AlgebraicCurve.ComponentChart.exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/32ae0b48-b87f-5981-82f3-cbf5e8afe3e5
-- title:
--   Chart units take unit values at some rational place
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $\kappa = \mathrm{ResidueField}\,A$; let $F$ be a field equipped with an $L$-algebra structure and $\bar F$ a field equipped with a $\kappa$-algebra structure. Here a place of $F/L$ is a valuation subring of $F$ containing the image of $L$, different from $F$ itself and a principal ideal ring, and $P.\mathrm{ord}$ denotes the associated normalised integer valuation. Assume: every non-zero $f \in F$ satisfies $P.\mathrm{ord}\,f = 0$ for all but finitely many places $P$ of $F/L$; the same finiteness holds for non-zero elements of $\bar F$ with respect to the places of $\bar F/\kappa$; and the set of all places of $\bar F/\kappa$ is infinite. Let $C$ be a component chart for $A$, $F$, $\bar F$, that is, a valuation subring $C.\mathrm{integers} \subseteq F$ together with a ring homomorphism $C.\mathrm{residue} : C.\mathrm{integers} \to \bar F$, a set $C.\mathrm{dom}$ of places of $F/L$, a finite set $C.\mathrm{nodes}$ of places of $\bar F/\kappa$ and a map $C.\mathrm{placeMap}$ from places of $F/L$ to places of $\bar F/\kappa$, subject to the axioms of `ComponentChart`: the image of $x \in L$ lies in $C.\mathrm{integers}$ exactly when $x \in A$, $C.\mathrm{residue}$ is surjective with kernel the maximal ideal of $C.\mathrm{integers}$ and is compatible with the residue map of $A$, every non-zero element of $F$ becomes, after scaling by a suitable element of $L$, an element of $C.\mathrm{integers}$ with non-zero reduction, $C.\mathrm{placeMap}$ avoids $C.\mathrm{nodes}$ on $C.\mathrm{dom}$, and the pointwise and divisor compatibilities between evaluation (resp. $\mathrm{ord}$) upstairs and downstairs hold. Assume further that every $P \in C.\mathrm{dom}$ is rational, meaning $L \to P.\mathrm{ResidueField}$ is surjective. Finally let $\iota$ be a finite index type and $f : \iota \to F$ a family such that each $f_i$ lies in $C.\mathrm{integers}$ and is a unit of that ring. The conclusion is that there exists $P \in C.\mathrm{dom}$ such that for every $i$ the element $f_i$ lies in the valuation subring of $P$ and its value $P.\mathrm{evalAt}\,f_i \in L$ lies in $A$ and is a unit of $A$.
--
--   This is the charted form of the density of rational (classical) points near the Gauss point of a component chart: finitely many unit conditions on the chart's ring of integers can be realised simultaneously at a single rational place of the chart's domain. It is used in the exhaustion arguments for type-II points on modular curves of full level, in the statements [`ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart`](thm.html#ModularCurve.FullLevel.typeII_exhaustion_of_placeCover_of_componentChart) and its variants at the primes $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.exists_mem_dom_forall_isUnit_evalAt_of_forall_isUnit
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (hfin : ∀ f : F, f ≠ 0 → Set.Finite {P : Place L F | P.ord f ≠ 0})
    (hfinb : ∀ g : Fbar, g ≠ 0 → Set.Finite {Q : Place (ResidueField A) Fbar | Q.ord g ≠ 0})
    (hinf : Set.Infinite (Set.univ : Set (Place (ResidueField A) Fbar)))
    (C : ComponentChart A F Fbar) (hrat : ∀ P ∈ C.dom, P.IsRational)
    {ι : Type} [Fintype ι] (f : ι → F) (hf : ∀ i, ∃ h : f i ∈ C.integers, IsUnit (⟨f i, h⟩ : C.integers)) :
    ∃ P ∈ C.dom, ∀ i, f i ∈ P.toValuationSubring ∧ ∃ h : P.evalAt (f i) ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
