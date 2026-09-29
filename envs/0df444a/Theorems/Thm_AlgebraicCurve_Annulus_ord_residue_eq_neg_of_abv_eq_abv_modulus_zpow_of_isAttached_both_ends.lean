-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/eb849c28-4e90-5135-8549-2172bd6d7459
-- title:
--   Equality case of the two-end law on an annulus
-- statement:
--   Fix a field $L$ with a valuation subring $A$, and a field $F$ over $L$ satisfying `HasPrincipalDivisors L F`, i.e. every $f \ne 0$ in $F$ is the divisor of a degree-zero divisor whose coefficient at each place $v$ of $F/L$ is $\mathrm{ord}_v f$ (minus the logarithm of the adic valuation attached to $v$); fix further two fields $\bar F,\bar F'$ over the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$. Let $An$, $An'$ be annuli over $A$ in $F$ — each consisting of a set `dom` of places, a parameter in $F$ and a modulus in the maximal ideal of $A$, subject to the rationality, divisibility, unique-evaluation, order-one and unit-principle axioms of `Annulus` (summarised here) — with the same domain and the same modulus $\pi$, with $\pi \ne 0$ in $L$, and with $An'.\mathrm{param}\cdot An.\mathrm{param}$ equal to the image of $\pi$ in $F$. Let $C$ be a component chart over $\bar F$ and $x$ a place of $\bar F$ over the residue field of $A$ with $An$ attached to $C$ at $x$, and likewise $C'$, $x'$ over $\bar F'$ with $An'$ attached to $C'$ at $x'$; attachment means $x$ lies in the chart's nodes, the annulus parameter lies in the chart's integers with $x$-order $1$ on its residue, and every chart-integral $f$ with non-zero residue and vanishing order along the annulus satisfies: $P.\mathrm{evalAt}(f)\cdot(P.\mathrm{evalAt}(\mathrm{param}))^{-\mathrm{ord}_x(\bar f)}$ is a unit of $A$ for every $P$ in the domain. Assume the annulus is wide, i.e. two places of the domain give different values $\mu(Q.\mathrm{evalAt}(An.\mathrm{param}))$. Let $h$ lie in the integers of $C$ with non-zero residue, put $a = \mathrm{ord}_x(C.\mathrm{residue}\,h)$, and let $c' \in A$ be non-zero with $(c')^{-1}h$ in the integers of $C'$ and with non-zero $C'$-residue. If $h$ has no pole on the annulus, i.e. $\mathrm{ord}_Q h \ge 0$ for all $Q$ in the domain, and $\mu(c') = \mu(\pi)^a$, then $\mathrm{ord}_Q h = 0$ for every $Q$ in the domain and $\mathrm{ord}_{x'}\big(C'.\mathrm{residue}((c')^{-1}h)\big) = -a$.
--
--   This is the extremal case of the two-end inequality $\mu(\pi)^a \le \mu(c')$ on a wide annulus: equality forces the function to be zero-free on the annulus and pins the order at the far end to $-a$. It is used in the study of multiplicative coverings of modular curves, where it yields that a family with the extremal content has vanishing orders along the annulus and reduction of order exactly $-1$ at the opposite node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.ord_residue_eq_neg_of_abv_eq_abv_modulus_zpow_of_isAttached_both_ends
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
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hca : μ c' = μ (An.modulus : L) ^ x.ord (C.residue ⟨h, hC⟩)) :
    (∀ Q ∈ An.dom, Q.ord h = 0) ∧
      x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = - x.ord (C.residue ⟨h, hC⟩) := by sorry
