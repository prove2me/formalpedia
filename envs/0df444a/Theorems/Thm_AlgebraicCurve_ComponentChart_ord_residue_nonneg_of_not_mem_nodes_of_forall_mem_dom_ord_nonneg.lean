-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
-- name    : AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/5423d70f-b8fc-5c3e-9733-9ebd126618f2
-- title:
--   Reduction of a pole-free chart unit is regular off nodes
-- statement:
--   Let $L$ be a field, $A$ a valuation subring of $L$, and $F$ a field extension of $L$ satisfying `HasPrincipalDivisors L F`, i.e. every nonzero $f \in F$ admits a finitely supported divisor $D : \mathrm{Place}\,L\,F \to\mathbb Z$ with $D(v) = v.\mathrm{ord}\,f$ for every place $v$ and $\deg D = 0$; here a place is a valuation subring of $F$ containing the image of $L$, proper and a principal ideal ring, and $\mathrm{ord}$ is minus the logarithm of its associated adic valuation. Let $\bar F$ be a field extension of the residue field of $A$, and let $C$ be a component chart of $F$ over $A$ with values in $\bar F$: a valuation subring $C.\mathrm{integers} \subseteq F$, a surjective ring homomorphism $C.\mathrm{residue}$ from it onto $\bar F$ with kernel the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$, a finite set $C.\mathrm{nodes}$ of places of $\bar F$ over the residue field of $A$, and a map $C.\mathrm{placeMap}$ on places, subject to the compatibility axioms of the structure (in particular: places in the domain do not reduce to nodes, and for a unit of $C.\mathrm{integers}$ the push-forward along $C.\mathrm{placeMap}$ of any divisor agreeing with its order function on $C.\mathrm{dom}$ and vanishing off $C.\mathrm{dom}$ computes the orders of its reduction at all non-node places). Let $g \in F$ be nonzero with $g \in C.\mathrm{integers}$ and $C.\mathrm{residue}\,g \neq 0$, and assume $0 \le P.\mathrm{ord}\,g$ for every place $P \in C.\mathrm{dom}$. Then for every place $v$ of $\bar F$ over the residue field of $A$ with $v \notin C.\mathrm{nodes}$ one has $0 \le v.\mathrm{ord}(C.\mathrm{residue}\,g)$.
--
--   This is the basic regularity statement for reductions along a component of a semistable model: a function that is a unit along the component and has no poles at the places of the domain reduces to a function on the component whose poles can only lie at the nodes. It is used throughout the construction of multiplicative coverings of modular curves, for instance to locate the poles of reductions of functions with poles only at a cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (g : F) (hg0 : g ≠ 0) (hg : g ∈ C.integers) (hres : C.residue ⟨g, hg⟩ ≠ 0)
    (hpole : ∀ P ∈ C.dom, 0 ≤ P.ord g)
    (v : Place (ResidueField A) Fbar) (hv : v ∉ C.nodes) :
    0 ≤ v.ord (C.residue ⟨g, hg⟩) := by sorry
