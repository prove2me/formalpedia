-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
-- name    : AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/12a341da-3194-5d7f-861a-9c94df83c5f0
-- title:
--   Maximum principle at the two ends of an attached annulus
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ in which principal divisors exist, i.e. each $f \neq 0$ admits a finitely supported divisor on the places of $F/L$ whose value at every place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$; let $F_a$, $F_b$ be fields over the residue field of $A$. Let $An$, $An'$ be annuli for $A$ in $F$ (each given by a set $\mathrm{dom}$ of places, a parameter and a modulus in the maximal ideal of $A$, with the structural axioms of `Annulus`) satisfying $An'.\mathrm{dom} = An.\mathrm{dom}$, $An'.\mathrm{modulus} = An.\mathrm{modulus}$, the image of $An.\mathrm{modulus}$ in $L$ nonzero, and $An'.\mathrm{param} \cdot An.\mathrm{param} =$ the image of $An.\mathrm{modulus}$ in $F$. Let $C_a$ be a component chart for $A$, $F$, $F_a$ and $x_a$ a rational place of $F_a$ over the residue field of $A$ (i.e. the structure map to its residue field is surjective) with $An$ attached to $(C_a, x_a)$: $x_a$ is a node of $C_a$, $An.\mathrm{param}$ lies in $C_a.\mathrm{integers}$ and its reduction has $x_a$-order $1$, and every $g \in C_a.\mathrm{integers}$ with nonzero reduction and $P.\mathrm{ord}\,g = 0$ for all $P \in An.\mathrm{dom}$ obeys the end-slope law: for each such $P$, $P.\mathrm{evalAt}\,g \cdot (P.\mathrm{evalAt}\,An.\mathrm{param})^{-\mathrm{ord}_{x_a}(\text{reduction of } g)}$ lies in $A$ and is a unit there. Let $(C_b, x_b)$ satisfy the same conditions with $An'$ in place of $An$. Finally let $f \in F$ lie in both $C_a.\mathrm{integers}$ and $C_b.\mathrm{integers}$ and satisfy $0 \le P.\mathrm{ord}\,f$ for all $P \in An.\mathrm{dom}$. Then: if the reduction of $f$ in $F_a$ is nonzero its $x_a$-order is $\ge 0$; if the reduction of $f$ in $F_b$ is nonzero its $x_b$-order is $\ge 0$; and the two values $x_a.\mathrm{evalAt}$ of the reduction in $F_a$ and $x_b.\mathrm{evalAt}$ of the reduction in $F_b$ agree in the residue field of $A$.
--
--   This is the maximum principle for a function bounded by $1$ at both ends of an annulus, expressed through the two charts to which the two presentations of the annulus are attached: no pole on the annulus forces the reductions to be regular at the two nodes and to take the same value there. It is used in the semistable covering results that glue local data into sections of a Riemann–Roch space and that compare residues across annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (IsLocalRing.ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : ((An.modulus : A) : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (Ca : ComponentChart A F Fa) (xa : Place (IsLocalRing.ResidueField A) Fa) (hxa : xa.IsRational)
    (hatta : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb) (hxb : xb.IsRational)
    (hattb : An'.IsAttached Cb xb)
    (f : F) (hfa : f ∈ Ca.integers) (hfb : f ∈ Cb.integers)
    (hreg : ∀ P ∈ An.dom, 0 ≤ P.ord f) :
    (Ca.residue ⟨f, hfa⟩ ≠ 0 → 0 ≤ xa.ord (Ca.residue ⟨f, hfa⟩)) ∧
    (Cb.residue ⟨f, hfb⟩ ≠ 0 → 0 ≤ xb.ord (Cb.residue ⟨f, hfb⟩)) ∧
    xa.evalAt (Ca.residue ⟨f, hfa⟩) = xb.evalAt (Cb.residue ⟨f, hfb⟩) := by sorry
