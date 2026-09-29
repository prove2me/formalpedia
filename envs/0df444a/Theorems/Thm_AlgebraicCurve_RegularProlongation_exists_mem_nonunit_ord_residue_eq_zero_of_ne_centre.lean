-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
-- name    : AlgebraicCurve.RegularProlongation.exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/793e5283-0a2d-59a3-836d-86a0498d0e71
-- title:
--   A chart element separating a place from the node
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, $F$ a field extension of $L$, and $FSS$ a field extension of the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $FSS$: a valuation subring $R.\mathrm{integers}$ of $F$ whose intersection with $L$ is $A$, together with a surjective ring homomorphism $R.\mathrm{residue}$ to $FSS$ with kernel the maximal ideal, compatible with reduction on $A$, and such that every nonzero $f\in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue. Let $O$ be a subring of $F$ which is local and all of whose elements lie in $R.\mathrm{integers}$, and $Bx$ a subring of $O$ such that every $f\in O$ can be written as $f=g/h$ with $g,h\in Bx$ and $h$ a unit of $O$ whenever it lies in $O$. Let $nd$ and $y$ be places of $FSS$ over the residue field of $A$, i.e. valuation subrings of $FSS$, proper, principal, containing the image of that residue field. Assume: any place $y'$ for which all residues of elements of $Bx$ lie in $y'$ and the residues of the elements of $Bx$ that are non-units of $O$ lie in the maximal ideal of $y'$ must equal $nd$; all residues of elements of $Bx$ lie in $y$; and $y\neq nd$. Then there is $g\in Bx$ which is not a unit of $O$ with $\mathrm{ord}_y(R.\mathrm{residue}(g))=0$ and $R.\mathrm{residue}(g)\neq 0$, where $\mathrm{ord}_y$ is minus the logarithm of the adic valuation attached to $y$.
--
--   This is the separation statement saying that an affine chart $Bx$ adapted to a node contains a function witnessing that a place $y$ distinct from the branch place $nd$ is not centred at the node: a chart element non-invertible at $O$ whose reduction is a unit at $y$. It feeds the construction of two-point functions in the layered node presentations of modular curves at full level, where $Bx$ is the node-adapted chart of a descended model and $nd$ the branch place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre.lean

import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre
    {L : Type} [Field L] (A : ValuationSubring L) {F : Type} [Field F] [Algebra L F]
    {FSS : Type} [Field FSS] [Algebra (ResidueField ↥A) FSS]
    (R : RegularProlongation A F FSS)
    (O : Subring F) [IsLocalRing ↥O] (hOR : ∀ f : F, f ∈ O → f ∈ R.integers)
    (Bx : Subring F) (hBO : Bx ≤ O)
    (hloc : ∀ f : F, f ∈ O ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
    (nd y : Place (ResidueField ↥A) FSS)

    (huniq : ∀ y' : Place (ResidueField ↥A) FSS,
      (∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring) →
      (∀ (b : F) (hb : b ∈ Bx), ¬ IsUnit (⟨b, hBO hb⟩ : ↥O) →
        ∃ hm : R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring, (⟨_, hm⟩ : ↥y'.toValuationSubring) ∈ maximalIdeal ↥y'.toValuationSubring) →
      y' = nd)
    (hy : ∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y.toValuationSubring)
    (hne : y ≠ nd) :
    ∃ (g : F) (hg : g ∈ Bx), ¬ IsUnit (⟨g, hBO hg⟩ : ↥O) ∧
      y.ord (R.residue ⟨g, hOR g (hBO hg)⟩) = 0 ∧ R.residue ⟨g, hOR g (hBO hg)⟩ ≠ 0 := by sorry
