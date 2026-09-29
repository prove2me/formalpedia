-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
-- name    : AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/13ebfa20-55d9-50bf-9db6-f19b5d5e6371
-- title:
--   Unique simple zero of a two-end function on an annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which every nonzero element has a degree-zero divisor supported on the places of $F/L$ (`HasPrincipalDivisors`), and let $\bar F, \bar F'$ be field extensions of the residue field of $A$. Assume $\mu$ is a real absolute value on $L$ with $A = \{a : \mu(a) \le 1\}$. Let $An, An'$ be annuli over $A$ in $F$ with the same domain of places and the same modulus $\pi$, with $\pi \ne 0$ in $L$ and with the two parameters satisfying $z' z = \pi$ in $F$. Suppose $An$ is attached to a component chart $C$ over $\bar F$ at a place $x$ of $\bar F$ over the residue field of $A$, and $An'$ is attached to a chart $C'$ over $\bar F'$ at a place $x'$, both $x$ and $x'$ being rational (the structure map from the residue field of $A$ to their residue fields is surjective); attachment means the place is a node of the chart, the parameter is integral on the chart with reduction of order $1$ at the place, and every chart-integral function with nonzero reduction and no zeros on the annulus has $P$-value times $(P\text{-value of the parameter})^{-\operatorname{ord}}$ a unit of $A$ at each $P$ of the domain. Assume the parameter takes two distinct absolute values on the domain, i.e. $\mu(Q_1(z)) \ne \mu(Q_2(z))$ for some $Q_1, Q_2$ in the domain, and that $z$ is $C$-integral. Let $h \in F$ be $C$-integral with nonzero reduction $\bar h$ of order exactly $1$ at $x$, let $c' \in L$ be nonzero and in $A$ with $c'^{-1}h$ being $C'$-integral with nonzero reduction of order $0$ at $x'$, and assume $\operatorname{ord}_Q h \ge 0$ for every place $Q$ of the domain. Then there is a place $Q$ of the domain with $\operatorname{ord}_Q h = 1$ and $\operatorname{ord}_P h = 0$ for every other place $P$ of the domain, with $\mu(Q(z)) = \mu(c')$, such that $Q(z)\,c'^{-1}$ lies in $A$ and is a unit there whose residue equals $-\,x'\!\left(\overline{c'^{-1}h}\right)\cdot\left(x\!\left(\bar h \cdot \bar z^{-1}\right)\right)^{-1}$, and such that for every place $R$ of the domain the value $R\!\left(h\,(z - Q(z))^{-1}\right)$ lies in $A$ and is a unit there with residue $x\!\left(\bar h \cdot \bar z^{-1}\right)$; here values of places are taken via `evalAt` and $\bar z$ denotes the reduction of $z$ on $C$.
--
--   This is the Weierstrass-type factorisation of a function on an annulus attached at both ends: the two-end data force the zero divisor on the annulus to consist of a single simple zero, whose position is pinned both in absolute value and in residue, and $h/(z - Q(z))$ is then a unit of constant residue across the annulus. It is used in the comparison of leading terms between inner annuli in the analysis of multiplicative coverings of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x) (hx : x.IsRational)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x') (hx' : x'.IsRational)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0) (hord : x.ord (C.residue ⟨h, hC⟩) = 1)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hord' : x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hz : An.param ∈ C.integers) :
    ∃ Q ∈ An.dom, Q.ord h = 1 ∧ (∀ P ∈ An.dom, P ≠ Q → P.ord h = 0) ∧
      μ (Q.evalAt An.param) = μ c' ∧
      (∃ hq : Q.evalAt An.param * c'⁻¹ ∈ A, IsUnit (⟨_, hq⟩ : A) ∧
        IsLocalRing.residue A ⟨_, hq⟩
          = -(x'.evalAt (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩))
              * (x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩)⁻¹))⁻¹) ∧
      ∀ R ∈ An.dom,
        ∃ hu : R.evalAt (h * (An.param - algebraMap L F (Q.evalAt An.param))⁻¹) ∈ A,
          IsUnit (⟨_, hu⟩ : A) ∧
          IsLocalRing.residue A ⟨_, hu⟩ = x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩)⁻¹) := by sorry
