-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/8ba9e707-7ecd-5b9a-aa59-55ae905d408a
-- title:
--   Far-end bound μ(c') μ(π)^{a'}≤ 1 on an annulus
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, and $F/L$ a field extension satisfying `HasPrincipalDivisors`, so that every nonzero element of $F$ is the support of a degree-zero divisor recording its orders at all places of $F/L$; let $Fbar$ and $Fbar'$ be fields over the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$, i.e. $a\in A \iff \mu(a)\le 1$. Let $An$ and $An'$ be annuli over $A$ in $F$ (each consisting of a set of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus`: rationality and parameter-value conditions at the places of the domain, unique realisation of admissible parameter values, $\operatorname{ord}_P(\mathrm{param}-\mathrm{param}(P))=1$, and a unit principle) with the same domain and the same modulus $\pi$, with $\pi\ne 0$ in $L$ and with the two parameters multiplying to $\pi$. Let $C$ be a component chart with residue field $Fbar$ and $x$ a place of $Fbar$ over the residue field of $A$ such that $An$ is attached to $(C,x)$, meaning $x$ is a node of $C$, the parameter of $An$ lies in $C.\mathrm{integers}$ with residue of $x$-order $1$, and every $C$-integral element with nonzero residue and vanishing order along $An.\mathrm{dom}$ becomes a unit of $A$ after rescaling by the appropriate power of the parameter value; let $(C',x')$ be such data for $An'$. Assume the annulus is wide, in the sense that two places of $An.\mathrm{dom}$ give different values of $\mu$ on the parameter. Finally let $h\in F$ lie in $C.\mathrm{integers}$ with nonzero $C$-residue and with $\operatorname{ord}_Q h\ge 0$ for all $Q\in An.\mathrm{dom}$, and let $c'\in A$, $c'\ne 0$, be such that $c'^{-1}h$ lies in $C'.\mathrm{integers}$ with nonzero $C'$-residue. Then $\mu(c')\,\mu(\pi)^{a'}\le 1$, where $a'=\operatorname{ord}_{x'}$ of the $C'$-residue of $c'^{-1}h$.
--
--   This is the far-end half of the two-end valuation law on an annulus: in valuation terms it says $a'\ge -v(c')/v(\pi)$, so the far-end reduction of the rescaled unit $c'^{-1}h$ has a pole at the node of order at most $v(c')/v(\pi)$. It is used in the rigidity and chord estimates for annuli and, downstream, in the bounds on the reductions of the good family along the cuspidal chart of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
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
    μ c' * μ (An.modulus : L) ^ x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ≤ 1 := by sorry
