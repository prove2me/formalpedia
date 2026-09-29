-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
-- name    : AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a15ead6f-92e0-50e8-83cc-42a0606b78c8
-- title:
--   Two-end zero count and radius product on an annulus
-- statement:
--   Fix a field $L$, a valuation subring $A \subseteq L$, a field extension $F/L$, and fields $F_a, F_b$ over the residue field $k$ of $A$. Let `An` be an annulus of $F/L$ along $A$: a set `An.dom` of places of $F/L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals), a parameter $z =$ `An.param` $\in F$ and a modulus $\pi =$ `An.modulus` $\in \mathfrak m_A$, such that each $P \in$ `An.dom` is rational with $z$ in its valuation ring, $z(P) := P.\mathrm{evalAt}(z)$ a nonzero element of $\mathfrak m_A$ dividing $\pi$ with quotient in $\mathfrak m_A$, every such admissible value occurring for exactly one $P \in$ `An.dom`, $\mathrm{ord}_P(z - z(P)) = 1$, and the unit principle holding; assume $\pi \neq 0$ in $L$. Let `Ra` be a regular prolongation of $A$ to $F$ with residue field $F_a$ (a valuation subring of $F$ whose intersection with $L$ is $A$, with surjective residue map of kernel the maximal ideal, compatible with $A \to k$, and with every nonzero element of $F$ scalable into it with nonzero residue), and $x_a$ a place of $F_a/k$, such that $z \in$ `Ra.integers`, $\mathrm{ord}_{x_a}(\mathrm{res}_a z) = 1$, and the end-slope law holds: any $f \in$ `Ra.integers` with $\mathrm{res}_a f \neq 0$ and $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom` satisfies that $f(P) z(P)^{-\mathrm{ord}_{x_a}(\mathrm{res}_a f)}$ lies in $A$ and is a unit there, for every $P \in$ `An.dom`. Let $(\mathrm{Rb}, x_b)$ be the same data for the reflected parameter $w = \pi z^{-1}$, namely $w \in$ `Rb.integers`, $\mathrm{ord}_{x_b}(\mathrm{res}_b w) = 1$, and the end-slope law with $w$ in place of $z$. Assume the annulus is wide: two places $Q_1, Q_2 \in$ `An.dom` with $v_A(z(Q_1)) \neq v_A(z(Q_2))$. Let $h \in F$ be nonzero, lying in `Ra.integers` with $\mathrm{res}_a h \neq 0$, and let $c' \in L$ be nonzero with $c'^{-1} h \in$ `Rb.integers` and $\mathrm{res}_b(c'^{-1}h) \neq 0$. Finally let $D$ be a divisor of $F/L$ (a finitely supported $\mathbb Z$-valued function on places) supported in `An.dom` and with $D(P) = \mathrm{ord}_P h$ for all $P \in$ `An.dom`. Then the total mass of $D$ equals $\mathrm{ord}_{x_a}(\mathrm{res}_a h) + \mathrm{ord}_{x_b}(\mathrm{res}_b(c'^{-1}h))$, and $\prod_P v_A(z(P))^{D(P)} = v_A(c')\, v_A(\pi)^{\mathrm{ord}_{x_b}(\mathrm{res}_b(c'^{-1}h))}$ in the value group of $A$ with zero.
--
--   This is the Newton-polygon description of the zeros and poles of a function on an annulus whose behaviour at the two ends is recorded by regular prolongations of $A$: the signed number of zeros is the drop of the dominant exponent between the ends, and the product of their radii is the ratio of dominant coefficients. It is the chart-free, valuation-theoretic form of the result, and it feeds the lemmas on functions without zeros or poles on an annulus, on attached charts, and on the fibre behaviour of semistable coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)

    (Ra : RegularProlongation A F Fa) (xa : Place (ResidueField A) Fa)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (Rb : RegularProlongation A F Fb) (xb : Place (ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))

    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ra.integers) (hresa : Ra.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Rb.integers) (hresb : Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)

    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h) :
    (D.sum fun _ n => n) = xa.ord (Ra.residue ⟨h, hha⟩) + xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) ∧
    (D.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation c' * A.valuation (An.modulus : L) ^ (xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)) := by sorry
