-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/0ef800da-0b9f-5004-8f41-d1a9084cca0f
-- title:
--   Two-end law on a doubly attached annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ whose nonzero elements all admit a degree-zero divisor recording their orders at every place of $F/L$ (`HasPrincipalDivisors`); let $Fbar$, $Fbar'$ be extensions of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$. Let $An$, $An'$ be annuli of $F$ over $A$, i.e. data consisting of a set of places of $F/L$, a parameter in $F$ and a modulus in the maximal ideal of $A$, subject to the annulus axioms (each place of the domain is rational, the parameter has value in the maximal ideal dividing the modulus, values of the parameter parametrise the domain bijectively, the parameter minus its value has order $1$, and the unit principle). Assume $An'$ and $An$ have the same domain and the same modulus $\pi$, that $\pi \neq 0$ in $L$, and that the product of the two parameters equals the image of $\pi$ in $F$. Let $C$ be a component chart for $A$, $F$, $Fbar$ (a valuation subring of $F$ with a surjective residue map to $Fbar$ whose kernel is the maximal ideal, together with a domain of places, a finite set of nodes, and a place map, satisfying the compatibility axioms) and $x$ a place of $Fbar$ over the residue field of $A$ with $An.\mathrm{IsAttached}\,C\,x$: $x$ is a node of $C$, the parameter of $An$ lies in the integers of $C$ and its residue has order $1$ at $x$, and every $f$ in the integers of $C$ with nonzero residue and with $\mathrm{ord}_P f = 0$ for all $P$ in the domain of $An$ satisfies that $f(P)\cdot(\text{param}(P))^{-\mathrm{ord}_x(\bar f)}$ is a unit of $A$ for all such $P$; similarly $C'$, $x'$ attached to $An'$ over $Fbar'$. Assume the domain of $An$ contains two places at which $\mu$ of the value of the parameter of $An$ differs. Let $h \in F$ lie in the integers of $C$ with nonzero residue, let $c' \in L$ be nonzero and in $A$ with $(c')^{-1}h$ in the integers of $C'$ and of nonzero residue there, and assume $\mathrm{ord}_Q h \geq 0$ for every $Q$ in the domain of $An$. Write $a := \mathrm{ord}_x$ of the $C$-residue of $h$ and $a' := \mathrm{ord}_{x'}$ of the $C'$-residue of $(c')^{-1}h$. The conclusion is threefold: $a + a' \geq 0$; for every place $R$ in the domain of $An$ one has $\mu(h(R)) \leq 1$, with $\mu(h(R)) < 1$ whenever $\mu(c') < 1$ or $a + a' > 0$; and if $\mu(c') = 1$ and $a = a' = 0$ then $\mathrm{ord}_R h = 0$ and $\mu(h(R)) = 1$ for every $R$ in the domain of $An$.
--
--   This is the non-archimedean maximum principle together with the zero-count law for a function on a closed annulus presented through charts: the quantity $a + a'$ is the number of zeros of $h$ on the annulus, and boundedness by $1$ at both ends forces boundedness, with strictness in the degenerate cases. It is the basic estimate used by the later annulus results, such as [`AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends`](thm.html#AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends) and the comparisons of $\mu$ of differences of values of $h$ with those of the parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
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
    0 ≤ x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ∧
    (∀ R ∈ An.dom, μ (R.evalAt h) ≤ 1 ∧
      ((μ c' < 1 ∨ 0 < x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩)) →
        μ (R.evalAt h) < 1)) ∧
    ((μ c' = 1 ∧ x.ord (C.residue ⟨h, hC⟩) = 0 ∧ x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = 0) →
      ∀ R ∈ An.dom, R.ord h = 0 ∧ μ (R.evalAt h) = 1) := by sorry
