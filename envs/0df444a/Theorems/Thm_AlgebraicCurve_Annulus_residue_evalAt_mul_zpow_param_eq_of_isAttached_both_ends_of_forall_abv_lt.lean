-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
-- name    : AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/b6f147b7-8170-5c07-9bbe-b89b5c27c9c1
-- title:
--   Leading term of a two-end unit at an outer place
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ having principal divisors (every nonzero element of $F$ is the support of a finitely supported divisor recording its orders at all places of $F/L$ and of degree $0$); let $\bar F$, $\bar F'$ be field extensions of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ with $a \in A \iff \mu(a) \le 1$. Let $An$, $An'$ be annuli over $A$ in $F$ with the same domain of places and the same modulus $\pi$, with $\pi \neq 0$ in $L$ and with $An'.\mathrm{param} \cdot An.\mathrm{param} = \pi$ in $F$. Let $C$ be a component chart over $\bar F$ and $x$ a place of $\bar F$ over the residue field of $A$ such that $An$ is attached to $C$ at $x$ (that is: $x$ is a node of $C$, the parameter $z := An.\mathrm{param}$ lies in $C.\mathrm{integers}$ and its $C$-residue has order $1$ at $x$, and for every $f \in C.\mathrm{integers}$ with nonzero $C$-residue and with $\mathrm{ord}_P f = 0$ for all $P \in An.\mathrm{dom}$, the element $f(P)\,z(P)^{-\mathrm{ord}_x(\bar f)}$ lies in $A$ and is a unit there, for every $P \in An.\mathrm{dom}$); assume moreover that $x$ is rational, i.e. the residue field of $A$ maps onto the residue field of $x$. Let likewise $C'$, $x'$ be a component chart over $\bar F'$ and a place to which $An'$ is attached. Assume the annulus is wide, in the sense that $\mu(z(Q_1)) \neq \mu(z(Q_2))$ for some $Q_1, Q_2 \in An.\mathrm{dom}$. Let $h \in F$ lie in $C.\mathrm{integers}$ with nonzero $C$-residue, and let $c' \in A$ be nonzero and such that $c'^{-1}h$ lies in $C'.\mathrm{integers}$ with nonzero $C'$-residue. Assume $\mathrm{ord}_Q h \ge 0$ for all $Q \in An.\mathrm{dom}$, and let $R \in An.\mathrm{dom}$ be such that $\mu(z(Q)) < \mu(z(R))$ for every $Q \in An.\mathrm{dom}$ with $\mathrm{ord}_Q h \neq 0$. Put $a := \mathrm{ord}_x(\bar h)$, the order at $x$ of the $C$-residue of $h$. Then $h(R)\,z(R)^{-a} \in A$, it is a unit of $A$, and its image in the residue field of $A$ equals the value at $x$ of $\bar h \cdot \bar z^{-a}$, evaluation at $x$ being taken in the residue field of $A$ via the rationality of $x$. Here $f(P)$ denotes $P.\mathrm{evalAt}\, f$, the image in $L$ of the $P$-residue of $f$ under the inverse of the residue field identification.
--
--   This is the non-archimedean statement that past the last break of its Newton polygon a function on an annulus is dominated by a single term: on the outer part of the annulus, beyond all zeros of $h$, the normalised value $h(R)z(R)^{-a}$ is a unit of $A$ whose reduction is the leading coefficient read off from the reduction of $h$ at the node $x$. It is used in the cross-comparison lemmas for pairs of annuli in the multiplicative covering of modular curves, where it identifies leading terms of functions on supersingular annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
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
    (R : Place L F) (hR : R ∈ An.dom)
    (hout : ∀ Q ∈ An.dom, Q.ord h ≠ 0 → μ (Q.evalAt An.param) < μ (R.evalAt An.param)) :
    ∃ hmem : R.evalAt h * (R.evalAt An.param) ^ (-(x.ord (C.residue ⟨h, hC⟩))) ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩
        = x.evalAt (C.residue ⟨h, hC⟩ * (C.residue ⟨An.param, hz⟩) ^ (-(x.ord (C.residue ⟨h, hC⟩)))) := by sorry
