-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
-- name    : AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/642ce309-92f6-501a-94ff-b3e612088726
-- title:
--   Newton-polygon identities for an annulus attached at both ends
-- statement:
--   Let $L$ be a field with valuation subring $A$, let $F$ be a field extension of $L$ satisfying `HasPrincipalDivisors L F` (every nonzero element of $F$ admits a finitely supported $D$ on the places of $F$ over $L$ with $D(v)=\operatorname{ord}_v$ of the element and $\deg D=0$), and let $\bar F$, $\bar F'$ be extensions of the residue field of $A$. Let $\mu$ be a real absolute value on $L$ with $A=\{a:\mu(a)\le 1\}$. Let $An$, $An'$ be annuli for $A$ in $F$ with the same domain $\mathrm{dom}$ of places and the same modulus $\pi\in\mathfrak m_A$, with $\pi\ne 0$ in $L$, and with parameters $z=An.\mathrm{param}$, $z'=An'.\mathrm{param}$ satisfying $z'z=\pi$ in $F$. Assume $An$ is attached to a component chart $C$ over $\bar F$ at a place $x$ of $\bar F$ over the residue field of $A$, and $An'$ to a chart $C'$ over $\bar F'$ at $x'$; attachment means the place is a node of the chart, the parameter lies in the chart's integer ring and its residue has order $1$ at that node, and for every $f$ in the chart's integer ring with nonzero residue and $\operatorname{ord}_P f=0$ for all $P\in\mathrm{dom}$, the element $P.\mathrm{evalAt}(f)\cdot (P.\mathrm{evalAt}(\mathrm{param}))^{-n}$ with $n$ the order at the node of the residue of $f$ lies in $A$ and is a unit there, for every $P\in\mathrm{dom}$. Assume further that $\mu(Q_1.\mathrm{evalAt}\,z)\ne\mu(Q_2.\mathrm{evalAt}\,z)$ for some $Q_1,Q_2\in\mathrm{dom}$. Finally let $h\in F$ lie in the integer ring of $C$ with nonzero residue, let $c'\in A$ be nonzero with $c'^{-1}h$ (formed via $\operatorname{algebraMap}$) in the integer ring of $C'$ with nonzero residue, and assume $\operatorname{ord}_Q h\ge 0$ for all $Q\in\mathrm{dom}$. Writing $a=x.\mathrm{ord}(C.\mathrm{residue}\,h)$ and $a'=x'.\mathrm{ord}(C'.\mathrm{residue}(c'^{-1}h))$, the conclusion is that there exists a finitely supported $D:\mathrm{Place}\,L\,F\to\mathbb Z$ with $D(Q)\ge 0$ for all $Q$, with $D$ supported inside $\mathrm{dom}$, with $D(Q)=\operatorname{ord}_Q h$ for all $Q\in\mathrm{dom}$, with $\sum_Q D(Q)=a+a'$, and with $$\sum_Q D(Q)\,\log\mu(Q.\mathrm{evalAt}\,z)=\log\mu(c')+a'\,\log\mu(\pi).$$
--
--   This is the non-archimedean Newton-polygon (product-formula) statement for a function on a closed annulus attached to semistable components at both of its ends: the zeros of $h$ in the annulus are counted by the two node orders, and their radii are constrained by a single logarithmic identity whose right-hand side records the normalising constant $c'$ and the modulus. It is the source of the subsequent bounds on $\mu$-values and on node orders along such an annulus, for instance [`AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends`](thm.html#AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
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
    ∃ D : Place L F →₀ ℤ, (∀ Q, 0 ≤ D Q) ∧ (∀ Q, D Q ≠ 0 → Q ∈ An.dom) ∧ (∀ Q ∈ An.dom, D Q = Q.ord h) ∧
      (D.sum fun _ m => m) = x.ord (C.residue ⟨h, hC⟩) + x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) ∧
      (D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt An.param)))
        = Real.log (μ c') + (x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) : ℝ) * Real.log (μ (An.modulus : L)) := by sorry
