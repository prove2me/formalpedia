-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c4b13990-c2c9-5878-b22f-0aa1f7e2455c
-- title:
--   Two-end bound μ(π)ᵃ≤μ(c') on an annulus
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, and $F$ a field extension of $L$ with principal divisors, i.e. every nonzero $f\in F$ is the divisor of a degree-zero element of the free abelian group on the places of $F$ over $L$ whose coefficient at each place $v$ is $\operatorname{ord}_v(f)$, the normalised valuation of $f$ at $v$. Let $\bar F$ and $\bar F'$ be extension fields of the residue field of $A$, and let $\mu$ be a real-valued absolute value on $L$ cutting out $A$, in the sense that $a\in A$ if and only if $\mu(a)\le 1$. Let $An$ and $An'$ be annuli over $A$ in $F$ (each given by a set of places of $F$ over $L$, a parameter, and a modulus in the maximal ideal of $A$, subject to the rationality, unique-parameter-value, order-one and unit axioms of the structure `Annulus`), with the same domain and the same modulus $\pi$, with $\pi\neq 0$ in $L$, and with the two parameters multiplying to the image of $\pi$ in $F$. Let $C$ be a component chart over $A$ in $F$ with residue field $\bar F$ and $x$ a place of $\bar F$ over the residue field of $A$ such that $An$ is attached to $C$ at $x$ (so $x$ is a node of $C$, the parameter of $An$ lies in the integers of $C$ and its reduction has order $1$ at $x$, and reductions of $C$-units with no zeros or poles on $An$ have their $x$-order matched by the slope of their values along $An$), and likewise let $An'$ be attached to a chart $C'$ with residue field $\bar F'$ at a place $x'$. Assume the domain of $An$ contains two places $Q_1,Q_2$ with $\mu(Q_1.\mathrm{evalAt}\,z)\neq\mu(Q_2.\mathrm{evalAt}\,z)$, where $z$ is the parameter of $An$ and $\mathrm{evalAt}$ denotes the $L$-valued evaluation of an element of $F$ at a place. Finally let $h\in F$ lie in the integers of $C$ with nonzero residue, let $c'\in L$ be nonzero and lie in $A$ with $(c')^{-1}h$ in the integers of $C'$ and with nonzero residue there, and assume $h$ has no pole on the annulus, $\operatorname{ord}_Q(h)\ge 0$ for all $Q$ in the domain of $An$. Then $\mu(\pi)^{a}\le\mu(c')$, the power being an integer power, where $a$ is the order at $x$ of the reduction of $h$ on $C$.
--
--   This is the quantitative form of the statement that rescaling a unit on one component into a unit on the neighbouring component across a tube of modulus $\pi$ costs a constant of absolute value at least $\mu(\pi)^{a}$, $a$ being the order of vanishing of the reduction at the node. It is used in the treatment of charts and chords on semistable curves, for instance in the rigidity and chord bounds for annuli attached at both ends and in the estimates for families over multiplicative coverings of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h) :
    μ (An.modulus : L) ^ x.ord (C.residue ⟨h, hC⟩) ≤ μ c' := by sorry
