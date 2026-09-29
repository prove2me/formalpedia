-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/bd95a85c-9df2-557f-b604-fd5ea0c40006
-- title:
--   Two-end maximum principle on an annulus, with scaling constant
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, and $F/L$ a field extension in which every nonzero element has a degree-zero principal divisor (`HasPrincipalDivisors`), and let $Fbar$, $Fbar'$ be fields over the residue field of $A$. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$, i.e. $a\in A \iff \mu(a)\le 1$. Let $An$, $An'$ be annuli along $A$ in $F$ — each given by a set of places of $F/L$, a parameter, and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus` — such that $An'.\mathrm{dom}=An.\mathrm{dom}$, $An'.\mathrm{modulus}=An.\mathrm{modulus}$, the modulus is nonzero in $L$, and the two parameters multiply to the image in $F$ of the modulus. Assume $An$ is attached to a component chart $C$ over $Fbar$ at a node $x$, and $An'$ to a component chart $C'$ over $Fbar'$ at a node $x'$; here attachment means that the node lies in the chart's set of nodes, the parameter is chart-integral with residue of order $1$ at the node, and every chart-integral element with nonzero residue and order $0$ at all places of the annulus has, at each such place $P$, the quantity $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}(\mathrm{param}))^{-x.\mathrm{ord}(\text{residue of } f)}$ a unit of $A$. Assume the annulus is wide, in the sense that $\mu(Q_1.\mathrm{evalAt}(An.\mathrm{param}))\neq\mu(Q_2.\mathrm{evalAt}(An.\mathrm{param}))$ for some $Q_1,Q_2\in An.\mathrm{dom}$. Finally let $g\in F$ be nonzero with $Q.\mathrm{ord}(g)\ge 0$ for all $Q\in An.\mathrm{dom}$, with $g$ integral for $C$, and let $b\in L$ be nonzero with $(b)^{-1}g$ integral for $C'$ (the inverse taken in $F$ of the image of $b$). Then for every $R\in An.\mathrm{dom}$ one has $\mu(R.\mathrm{evalAt}(g))\le\max(1,\mu(b))$, and moreover $\mu(R.\mathrm{evalAt}(g))<\max(1,\mu(b))$ whenever $\mu(b)\neq 1$.
--
--   This is a maximum principle for a function on an annulus that is attached at both of its ends to component charts of a semistable model: integrality at one end and integrality after scaling by a constant $b$ at the other bound the values on the whole annulus by $\max(1,\mu(b))$, strictly unless $\mu(b)=1$, with no hypothesis on residues. It is used in the comparison of values across an annulus and in the analysis of annuli attached at both ends in a certified family of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends
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
    (g : F) (hg0 : g ≠ 0) (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord g)
    (hgC : g ∈ C.integers) (b : L) (hb0 : b ≠ 0) (hgC' : (algebraMap L F b)⁻¹ * g ∈ C'.integers) :
    ∀ R ∈ An.dom, μ (R.evalAt g) ≤ max 1 (μ b) ∧ (μ b ≠ 1 → μ (R.evalAt g) < max 1 (μ b)) := by sorry
