-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt
-- name    : AlgebraicCurve.Annulus.exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/e953a64f-89d0-50be-91a7-fb9c57b694e6
-- title:
--   Mirror law for distances strictly inside the critical circle
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which every nonzero element has a degree-zero divisor recording its orders at all places of $F/L$ (`HasPrincipalDivisors`); let $\bar F$, $\bar F'$ be fields over the residue field of $A$. Let $\mu$ be a nonarchimedean real absolute value on $L$ whose closed unit ball is exactly $A$. Let $\mathrm{An}$, $\mathrm{An}'$ be annuli over $A$ in $F$ (each a set $\mathrm{dom}$ of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the rationality, evaluation-bijectivity, $\mathrm{ord}(\text{param}-\text{value})=1$ and unit-normalisation axioms) with the same domain and the same nonzero modulus $m$, their parameters $z'$, $z$ satisfying $z' z = m$ in $F$; let $\mathrm{An}$ be attached to a node $x$ of a component chart $C$ over $\bar F$ and $\mathrm{An}'$ to a node $x'$ of a chart $C'$ over $\bar F'$, and assume two places of $\mathrm{An}.\mathrm{dom}$ give parameter values of distinct $\mu$-absolute value. Let $h \in F$ lie in $C.\mathrm{integers}$ with nonzero $C$-reduction of order $1$ at $x$, with $\mathrm{ord}_Q h \ge 0$ for all $Q$ in the domain; let $c' \in A$, $c' \ne 0$, be such that $c'^{-1}h$ lies in $C'.\mathrm{integers}$ with nonzero $C'$-reduction of order $0$ at $x'$, and assume some $\kappa_0$ in the residue field of $A$ satisfies $\mathrm{ord}_{x'}\bigl(\overline{c'^{-1}h} - \kappa_0\bigr) = 1$. Then for every $Q$ in the domain with $\mu(z(Q)) < \mu(c')$ there is $Q^{*}$ in the domain with $\mu(z(Q))\,\mu(z(Q^{*})) = \mu(c')\,\mu(m)$ and, for all $P$ in the domain, $$\mu\bigl(h(P)-h(Q)\bigr)\,\mu\bigl(z'(Q^{*})\bigr) = \mu\bigl(z(P)-z(Q)\bigr)\,\mu\bigl(z'(P)-z'(Q^{*})\bigr),$$ where $f(P)$ denotes the value $P.\mathrm{evalAt}\,f \in L$ obtained from the residue of $f$ at the place $P$.
--
--   This is a mirror, or reciprocity, law for the $\mu$-distance function attached to $h$ on an annulus attached to nodes at both ends: for places strictly inside the circle $\mu(z) = \mu(c')$, the distance $|h(P)-h(Q)|$ is computed by the two annulus parameters at the reflected place $Q^{*}$. It is used in the comparison of annuli in [`ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily`](thm.html#ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμ' : IsNonarchimedean μ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0) (hord : x.ord (C.residue ⟨h, hC⟩) = 1)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hord' : x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (κ₀ : ResidueField A)
    (hunr : x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ - algebraMap (ResidueField A) Fbar' κ₀) = 1) :
    ∀ Q ∈ An.dom, μ (Q.evalAt An.param) < μ c' →
      ∃ Qs ∈ An.dom, μ (Q.evalAt An.param) * μ (Qs.evalAt An.param) = μ c' * μ (An.modulus : L) ∧
        ∀ P ∈ An.dom, μ (P.evalAt h - Q.evalAt h) * μ (Qs.evalAt An'.param)
          = μ (P.evalAt An.param - Q.evalAt An.param) * μ (P.evalAt An'.param - Qs.evalAt An'.param) := by sorry
