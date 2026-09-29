-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
-- name    : AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4cd925b6-c751-5c5c-97df-9b8a5ae3f5c4
-- title:
--   Width-one two-end unit is an isometry on an attached annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which every nonzero element has a divisor of degree zero (its order at every place of $F/L$, all but finitely many being zero). Let $\bar F$ and $\bar F'$ be extensions of the residue field of $A$. Let $\mu$ be a real-valued absolute value on $L$ whose unit ball is exactly $A$, i.e. $a \in A \iff \mu(a) \le 1$. Let $An$ and $An'$ be annuli of $F$ over $A$ (each given by a set of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the rationality, valuation, uniqueness, simple-zero and unit axioms of `Annulus`) with the same set of places, $An'.\mathrm{dom} = An.\mathrm{dom}$, the same modulus $\pi$, nonzero in $L$, and parameters satisfying $An'.\mathrm{param} \cdot An.\mathrm{param} = \pi$ in $F$. Assume $An$ is attached to a component chart $C$ over $\bar F$ at a node $x$ and $An'$ to a component chart $C'$ over $\bar F'$ at a node $x'$; here attachment means the node lies in the chart's nodes, the parameter is integral for the chart with reduction of order $1$ at the node, and for every chart-integral element with nonzero reduction and no zeros on the annulus the value at each place of the annulus, divided by the corresponding power of the parameter's value given by the order of the reduction at the node, is a unit of $A$. Assume further that $An.\mathrm{param}$ takes two different absolute values at two places of $An.\mathrm{dom}$, and let $f \in F$ be integral for $C$ with nonzero reduction whose order at $x$ equals $1$, such that $\pi^{-1} f$ is integral for $C'$ with nonzero reduction, and such that $f$ lies in the valuation ring of every place of $An.\mathrm{dom}$. Then $f$ has order $0$ at every place of $An.\mathrm{dom}$, and for all places $P, Q$ of $An.\mathrm{dom}$, writing $g(P)$ for the value in $L$ of $g$ at the rational place $P$, $$\mu\bigl(f(P)\bigr) = \mu\bigl(An.\mathrm{param}(P)\bigr), \qquad \mu\bigl(f(P) - f(Q)\bigr) = \mu\bigl(An.\mathrm{param}(P) - An.\mathrm{param}(Q)\bigr).$$
--
--   This is the abstract 'width one' comparison: an element with a simple zero of its reduction at the near node and scaled by exactly the modulus at the far node induces an isometry, in the absolute value $\mu$, of the annulus onto the annulus of parameter values. It is used by [`ModularCurve.annulusComparison_of_attached_at_both_ends_of_adaptedFamily`](thm.html#ModularCurve.annulusComparison_of_attached_at_both_ends_of_adaptedFamily) to compare a member of an adapted family with the parameter of a supersingular tube $xy = \pi$ attached at both of its ends.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_isAttached_both_ends_of_ord_residue_eq_one
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
    (f : F) (hC : f ∈ C.integers) (hres : C.residue ⟨f, hC⟩ ≠ 0) (hord : x.ord (C.residue ⟨f, hC⟩) = 1)
    (hC' : (algebraMap L F (An.modulus : L))⁻¹ * f ∈ C'.integers)
    (hres' : C'.residue ⟨(algebraMap L F (An.modulus : L))⁻¹ * f, hC'⟩ ≠ 0)
    (hreg : ∀ R ∈ An.dom, f ∈ R.toValuationSubring) :
    (∀ R ∈ An.dom, R.ord f = 0) ∧
    ∀ P ∈ An.dom, ∀ Q ∈ An.dom,
      μ (P.evalAt f) = μ (P.evalAt An.param) ∧
      μ (P.evalAt f - Q.evalAt f) = μ (P.evalAt An.param - Q.evalAt An.param) := by sorry
