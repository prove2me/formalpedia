-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_componentChart_of_discFamily
-- name    : AlgebraicCurve.RegularProlongation.exists_componentChart_of_discFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/d78eb740-09a2-5bc9-b26d-8db0d4f99fd9
-- title:
--   Component chart from a regular prolongation and a disc family
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $\kappa = \mathrm{ResidueField}(A)$, let $F$ be a field extension of $L$ and $\bar F$ a field extension of $\kappa$. Let $R$ be a regular prolongation of $A$ to $F$ over $\bar F$, that is: a valuation subring $R.\mathrm{integers} \subseteq F$ together with a surjective ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ whose kernel is the maximal ideal, such that $\mathrm{algebraMap}(x) \in R.\mathrm{integers}$ iff $x \in A$ for $x \in L$, such that the residue map is compatible with $A \to \kappa \to \bar F$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue. Let $N$ be a finite set of places of $\bar F$ over $\kappa$, assume the type of such places is nonempty, and let $\mathrm{disc}$ assign to each such place a set of places of $F$ over $L$ and $\mathrm{coord}$ assign to each an element of $F$, with $R.\mathrm{DiscFamily}\,N\,\mathrm{disc}\,\mathrm{coord}$: for every $Q \notin N$ the triple $(Q, \mathrm{disc}(Q), \mathrm{coord}(Q))$ satisfies the three residue-disc conditions `IsDiscCoord`, `PointwiseOn` and `DegreeOn` of $R$, and the sets $\mathrm{disc}(Q)$ for distinct $Q, Q' \notin N$ are disjoint. The conclusion is the existence of a component chart $C$ of $F$ along $A$ over $\bar F$ (a structure carrying integers, a residue map, a domain of places, a node set, a place map, the same local axioms as a regular prolongation, and the two compatibility axioms `pointwise` and `mapDomain_placeMap`) with $C.\mathrm{integers} = R.\mathrm{integers}$, with $C.\mathrm{residue}$ and $R.\mathrm{residue}$ agreeing on every element of the common ring of integers, with $C.\mathrm{nodes} = N$, with $C.\mathrm{dom}$ equal to the set of places lying in $\mathrm{disc}(Q)$ for some $Q \notin N$, and with $C.\mathrm{placeMap}(P) = Q$ whenever $Q \notin N$ and $P \in \mathrm{disc}(Q)$.
--
--   This is the chart-construction step: it produces a component chart at a type-II point of the curve — for instance at the Gauss point of a Drinfeld or Igusa component of a stable reduction — out of a regular prolongation together with the residue discs of its non-node directions, the chart's domain being the union of those discs and its place map recording which disc a place lies in. Note that $N$ is only required to contain the directions for which no disc is given: a direction carrying a disc may still be declared a node, in which case its disc is simply left out of the chart's domain. It is used in the construction of semistable coverings of modular curves of full level, in the verification of the Drinfeld clause for valuation subrings over a fixed one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_componentChart_of_discFamily.lean

import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.RegularProlongation.exists_componentChart_of_discFamily
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (N : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar))
    (hne : Nonempty (AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar))
    (disc : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar → Set (AlgebraicCurve.Place L F))
    (coord : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar → F)
    (hfam : R.DiscFamily N disc coord) :
    ∃ C : AlgebraicCurve.ComponentChart A F Fbar,
      C.integers = R.integers ∧
      (∀ (f : F) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) ∧
      C.nodes = N ∧
      (∀ P, P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
      (∀ P Q, Q ∉ N → P ∈ disc Q → C.placeMap P = Q) := by sorry
