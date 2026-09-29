-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation
-- name    : AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/8f3204d9-a050-506a-9cfe-a3f95211b5ee
-- title:
--   Unit reduction on an annulus equals its value at the node
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, $F$ a field extension of $L$ in which every nonzero element has a finitely supported divisor of degree $0$ recording its orders at all places of $F/L$, and $F_a$ a field extension of the residue field of $A$. Let `An` be an annulus of $F/L$ over $A$, with domain `An.dom` a set of places of $F/L$ and parameter `An.param`, let `Ra` be a regular prolongation of $A$ to $F$ with values in $F_a$ (a valuation subring `Ra.integers` of $F$ together with a surjective ring map `Ra.residue` onto $F_a$ whose kernel is the maximal ideal, compatible with $A$), and let $x_a$ be a place of $F_a$ over the residue field of $A$. Assume: `An.param` lies in `Ra.integers` and its residue has $\operatorname{ord}_{x_a}=1$; the end-slope law, namely that for every $f\in$ `Ra.integers` with nonzero residue and with $\operatorname{ord}_P f=0$ for all $P\in$ `An.dom`, the element $f(P)\cdot \mathrm{param}(P)^{-\operatorname{ord}_{x_a}\bar f}$ lies in $A$ and is a unit there, for every such $P$; and that $x_a$ is rational, i.e. the residue field of $A$ surjects onto that of $x_a$. Let $u\in$ `Ra.integers` have nonzero residue $\bar u$ with $\operatorname{ord}_{x_a}\bar u=0$ and satisfy $\operatorname{ord}_P u=0$ for all $P\in$ `An.dom`. Then for every $P\in$ `An.dom` the value $u(P)=$ `P.evalAt u` lies in $A$, is a unit of $A$, and its residue class in the residue field of $A$ equals $x_a$-value of $\bar u$, i.e. `xa.evalAt (Ra.residue ⟨u, hu⟩)`.
--
--   This is the end-reading step for annuli: it identifies the constant reduction of a zero- and pole-free unit over the domain of the annulus with the value, at the place $x_a$, of its reduction at the prolongation, the regular case $\operatorname{ord}_{x_a}\bar u=0$ being the one where that value is a unit. It is used in [`AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne`](thm.html#AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne), and rests on the interior constancy statement [`AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit`](thm.html#AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit) together with the elementary calculus of `evalAt` for rational places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_ord_residue_eq_zero_of_regularProlongation
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (IsLocalRing.ResidueField A) Fa]
    (An : Annulus A F)
    (Ra : RegularProlongation A F Fa) (xa : Place (IsLocalRing.ResidueField A) Fa)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hxa_rat : xa.IsRational)
    (u : F) (hu : u ∈ Ra.integers) (hres : Ra.residue ⟨u, hu⟩ ≠ 0)
    (hord : xa.ord (Ra.residue ⟨u, hu⟩) = 0)
    (hzero : ∀ P ∈ An.dom, P.ord u = 0) :
    ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨_, h⟩ : A) ∧
      IsLocalRing.residue A ⟨P.evalAt u, h⟩ = xa.evalAt (Ra.residue ⟨u, hu⟩) := by sorry
