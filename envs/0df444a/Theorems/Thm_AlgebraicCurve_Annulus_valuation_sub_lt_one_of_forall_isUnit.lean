-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit
-- name    : AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4ad518e3-a3ea-5aa8-a328-e52596eb8a8b
-- title:
--   Units from the annulus unit principle have constant residue
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure in which every nonzero element has a finitely supported divisor, indexed by the places of $F$ over $L$ (valuation subrings of $F$ containing the image of $L$, proper, and principal ideal rings), whose value at each place $P$ is $P.\mathrm{ord}$ of the element and whose degree is $0$. Let `An` be an annulus of $F$ over $A$: a set `An.dom` of places, a parameter `An.param` $=z$, and a modulus in the maximal ideal of $A$, such that each $P\in$ `An.dom` is rational (the map from $L$ to its residue field is surjective) with $z$ in the valuation ring of $P$ and value $z(P)\in A$ nonzero and in the maximal ideal, with the modulus equal to $z(P)$ times a maximal-ideal element; each such admissible value is attained by $z$ at exactly one place of the domain; $z-z(P)$ has $P$-order $1$; and the unit principle holds. Let $f\in F$ be nonzero with $P.\mathrm{ord}\,f=0$ for all $P\in$ `An.dom`, let $m\in\mathbb Z$ and $c\in L$, $c\neq 0$, be such that $f(P)c^{-1}z(P)^{-m}$ lies in $A$ and is a unit there for every $P\in$ `An.dom`. Then for all $P,Q\in$ `An.dom`, the valuation attached to $A$ of $f(P)c^{-1}z(P)^{-m}-f(Q)c^{-1}z(Q)^{-m}$ is $<1$.
--
--   Here $f(P)$ denotes the value at $P$, i.e. the element of $L$ obtained from the residue of $f$ in the residue field of $P$ by inverting the map from $L$; the conclusion says that the unit supplied by the unit principle of an annulus has one and the same residue in the residue field of $A$ at all places of the annulus, the value-level counterpart of the classical fact that an invertible analytic function on an annulus is $c\,z^{m}(1+h)$ with $|h|<1$. It is used in the construction of attached charts and in the comparison of residues of values with values of residues along regular prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (An : Annulus A F) (f : F) (hf0 : f ≠ 0) (hf : ∀ P ∈ An.dom, P.ord f = 0)
    (m : ℤ) (c : L) (hc : c ≠ 0)
    (hu : ∀ P ∈ An.dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A))
    (P Q : Place L F) (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    A.valuation (P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) -
      Q.evalAt f * c⁻¹ * (Q.evalAt An.param) ^ (-m)) < 1 := by sorry
