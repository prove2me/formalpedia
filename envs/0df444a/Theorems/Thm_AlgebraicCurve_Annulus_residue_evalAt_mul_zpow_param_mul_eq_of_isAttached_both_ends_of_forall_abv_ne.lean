-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne
-- name    : AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/182c0eaa-c793-5d36-b41e-e7c89a6a227a
-- title:
--   Band-wise leading coefficient of a two-end annulus unit
-- statement:
--   Fix a field $L$, a valuation subring $A \subseteq L$ and a field extension $F/L$ in which every nonzero element has a divisor of degree zero, together with extensions $\bar F$, $\bar F'$ of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ cutting out $A$, i.e. $a \in A \iff \mu(a) \le 1$. Let $An$, $An'$ be annuli over $A$ in $F$ with the same set of places, $An'.\mathrm{dom} = An.\mathrm{dom}$, the same modulus $\pi$, with $\pi \ne 0$ in $L$, and with parameters satisfying $An'.\mathrm{param} \cdot An.\mathrm{param} = \pi$ in $F$; write $z := An.\mathrm{param}$. Let $C$ be a component chart over $\bar F$ and $x$ a place of the residue field of $A$ in $\bar F$ with $An$ attached to $C$ at $x$ (so $x$ is a node of $C$, $z$ lies in the integers of $C$, $x.\mathrm{ord}$ of its $C$-residue is $1$, and every $C$-unit with nonvanishing residue which has order zero at all places of $An.\mathrm{dom}$ satisfies the unit law $P.\mathrm{evalAt}(f)\, P.\mathrm{evalAt}(z)^{-x.\mathrm{ord}(\bar f)} \in A^{\times}$), and assume $x$ is rational, i.e. the residue field of $A$ surjects onto the residue field of $x$. Let likewise $C'$, $x'$ be a chart and a place with $An'$ attached to $C'$ at $x'$. Assume the annulus has two radii: some $Q_1, Q_2 \in An.\mathrm{dom}$ with $\mu(Q_1.\mathrm{evalAt}\,z) \ne \mu(Q_2.\mathrm{evalAt}\,z)$. Let $h \in F$ lie in the integers of $C$ with nonzero $C$-residue, and let $c' \in L$ be nonzero and in $A$ with $c'^{-1}h$ in the integers of $C'$ and with nonzero $C'$-residue; assume $0 \le Q.\mathrm{ord}(h)$ for all $Q \in An.\mathrm{dom}$. Let $D$ be a finitely supported integer-valued function on the places of $F/L$ with $D \ge 0$, support contained in $An.\mathrm{dom}$, and $D(Q) = Q.\mathrm{ord}(h)$ for $Q \in An.\mathrm{dom}$. Finally let $R \in An.\mathrm{dom}$ satisfy $\mu(Q.\mathrm{evalAt}\,z) \ne \mu(R.\mathrm{evalAt}\,z)$ for every $Q$ in the support of $D$. Put $a := x.\mathrm{ord}$ of the $C$-residue of $h$, $N(R) := \sum_{\mu(Q.\mathrm{evalAt}\,z) > \mu(R.\mathrm{evalAt}\,z)} D(Q)$ and $c(R) := \prod_{\mu(Q.\mathrm{evalAt}\,z) > \mu(R.\mathrm{evalAt}\,z)} (-(Q.\mathrm{evalAt}\,z))^{D(Q)}$. The conclusion is that $R.\mathrm{evalAt}(h) \cdot (R.\mathrm{evalAt}\,z)^{-(a - N(R))} \cdot c(R)^{-1}$ lies in $A$, is a unit there, and its image in the residue field of $A$ equals the value at $x$ of the $C$-residue of $h$ times the $(-a)$-th power of the $C$-residue of $z$.
--
--   This is the Newton-polygon description of a function that is a unit at both ends of an annulus: on each band between consecutive critical circles it is a monomial $c(R)\,z^{a-N(R)}$ times a unit whose residue is the leading coefficient of the reduction of $h$ read at the node $x$ on the $C$-branch, the slope dropping by the multiplicity of the zeros at each critical circle. It is used in the cross-comparison of charts along a multiplicative covering of a modular curve, via [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_twoMembers`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_twoMembers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (hx : x.IsRational)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hz : An.param ∈ C.integers)
    (D : Place L F →₀ ℤ) (hD0 : ∀ Q, 0 ≤ D Q) (hDdom : ∀ Q, D Q ≠ 0 → Q ∈ An.dom)
    (hD : ∀ Q ∈ An.dom, D Q = Q.ord h)
    (R : Place L F) (hR : R ∈ An.dom)
    (hcrit : ∀ Q, D Q ≠ 0 → μ (Q.evalAt An.param) ≠ μ (R.evalAt An.param)) :
    ∃ hmem : R.evalAt h
        * (R.evalAt An.param) ^ (-(x.ord (C.residue ⟨h, hC⟩)
              - (D.sum fun Q m => if μ (R.evalAt An.param) < μ (Q.evalAt An.param) then m else 0)))
        * (D.prod fun Q m => if μ (R.evalAt An.param) < μ (Q.evalAt An.param)
              then (-(Q.evalAt An.param)) ^ m else 1)⁻¹ ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩
        = x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩) ^ (-(x.ord (C.residue ⟨h, hC⟩)))) := by sorry
