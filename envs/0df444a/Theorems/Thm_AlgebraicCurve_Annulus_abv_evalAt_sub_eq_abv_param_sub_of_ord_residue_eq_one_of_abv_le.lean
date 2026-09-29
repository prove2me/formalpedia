-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le
-- name    : AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/dca0565b-fbad-5a06-83cd-d9e3c0a8836a
-- title:
--   Isometry of a two-end unit above the radius μ(c')
-- statement:
--   Let $L$ be a field, $A$ a valuation subring of $L$, and $F$ a field extension of $L$ in which every nonzero element has a degree-zero divisor recording its orders at all places of $F/L$; let $\bar F$ and $\bar F'$ be extensions of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ that is nonarchimedean and whose unit ball is exactly $A$ (i.e. $a\in A \iff \mu(a)\le 1$). Let $An$, $An'$ be annuli over $A$ in $F$ with the same domain of places and the same modulus, the modulus nonzero in $L$, and with parameters satisfying $An'.\mathrm{param}\cdot An.\mathrm{param} = \mathrm{algebraMap}\,(An.\mathrm{modulus})$. Let $C$ be a component chart over $\bar F$ and $x$ a place of the residue field of $A$ in $\bar F$ with `An.IsAttached C x` — that is, $x$ is a node of $C$, the parameter of $An$ is $C$-integral with reduction of order $1$ at $x$, and for every $C$-integral $f$ with nonzero reduction and $P.\mathrm{ord}\,f = 0$ throughout the domain, $P.\mathrm{evalAt}(f)\cdot(P.\mathrm{evalAt}(An.\mathrm{param}))^{-x.\mathrm{ord}(C.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there; likewise let $C'$, $x'$ satisfy `An'.IsAttached C' x'`. Assume the annulus is wide, in the sense that two places $Q_1,Q_2$ of the domain give $\mu(Q_1.\mathrm{evalAt}(An.\mathrm{param})) \neq \mu(Q_2.\mathrm{evalAt}(An.\mathrm{param}))$. Let $h\in F$ be $C$-integral with nonzero reduction of order exactly $1$ at $x$, let $c'\in L$ be nonzero and in $A$ with $(c')^{-1}h$ being $C'$-integral with nonzero reduction of order $0$ at $x'$, and assume $h$ has no pole on the annulus, $0\le Q.\mathrm{ord}\,h$ for all $Q$ in the domain. Then for all places $P, Q$ of the domain with $\mu(c')\le\mu(Q.\mathrm{evalAt}(An.\mathrm{param}))$ one has $\mu(P.\mathrm{evalAt}(h)-Q.\mathrm{evalAt}(h)) = \mu(P.\mathrm{evalAt}(An.\mathrm{param})-Q.\mathrm{evalAt}(An.\mathrm{param}))$.
--
--   This is the isometry statement for a function with a single simple zero on an annulus attached at both ends: above the critical radius $\mu(c')$, the function $h$ reproduces the distances measured by the annulus parameter. It is used in the comparison of annuli for certified families on modular curves, via [`ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily`](thm.html#ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le
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
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h) :
    ∀ P ∈ An.dom, ∀ Q ∈ An.dom, μ c' ≤ μ (Q.evalAt An.param) →
      μ (P.evalAt h - Q.evalAt h) = μ (P.evalAt An.param - Q.evalAt An.param) := by sorry
