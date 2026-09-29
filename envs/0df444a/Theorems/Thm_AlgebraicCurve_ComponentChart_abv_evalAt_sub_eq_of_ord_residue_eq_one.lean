-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one
-- name    : AlgebraicCurve.ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/2812e870-3bbc-5d77-9528-0a46167e5152
-- title:
--   Two simple uniformisers on a residue fibre give equal distances
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F/L$ a field extension in which every nonzero element has a degree-zero principal divisor (the class `HasPrincipalDivisors`), and $\bar F$ an extension of the residue field of $A$. Let $C$ be a component chart: a valuation subring $C.\mathrm{integers}$ of $F$ together with a surjective ring map $C.\mathrm{residue}$ onto $\bar F$ with kernel the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$ (each a proper valuation subring of $F$ containing $L$ and a principal ideal ring), a finite set of nodes among the places of $\bar F$ over the residue field of $A$, and a reduction map $C.\mathrm{placeMap}$, subject to the chart axioms. Let $\mu$ be a real absolute value on $L$ whose unit ball is exactly $A$, let $P \in C.\mathrm{dom}$, and assume every place in $C.\mathrm{dom}$ is rational, i.e. $L$ surjects onto its residue field, so that the evaluation $w.\mathrm{evalAt}$ (the chosen $L$-preimage of the residue, and $0$ off the valuation subring) is defined. Let $\rho, T \in F$ be such that $\rho - \rho(P)$ and $T - T(P)$ lie in $C.\mathrm{integers}$ with nonzero reductions in $\bar F$, both reductions having $\mathrm{ord} = 1$ at the place $C.\mathrm{placeMap}\,P$, and such that $\rho$ and $T$ lie in the valuation subring of every $w \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,w = C.\mathrm{placeMap}\,P$. Then for every $Q \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,Q = C.\mathrm{placeMap}\,P$ one has $\mu(T(Q) - T(P)) = \mu(\rho(Q) - \rho(P))$.
--
--   This is the statement that on a single residue fibre of a component chart the distance function attached to a parameter is independent of the choice of parameter, provided the translated parameter reduces to a function with a simple zero at the reduction point: classically, the invariance of the metric on a residue disc under change of étale coordinate. It is used in the comparison of chart data, via [`AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec`](thm.html#AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec), to transfer estimates stated for one chart parameter into estimates for another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (P : Place L F) (hP : P ∈ C.dom) (hrat : ∀ w ∈ C.dom, w.IsRational)
    (ρ T : F)
    (hρ : ρ - algebraMap L F (P.evalAt ρ) ∈ C.integers) (hρ0 : C.residue ⟨_, hρ⟩ ≠ 0)
    (hρ1 : (C.placeMap P).ord (C.residue ⟨_, hρ⟩) = 1)
    (hρreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ ∈ w.toValuationSubring)
    (hT : T - algebraMap L F (P.evalAt T) ∈ C.integers) (hT0 : C.residue ⟨_, hT⟩ ≠ 0)
    (hT1 : (C.placeMap P).ord (C.residue ⟨_, hT⟩) = 1)
    (hTreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T ∈ w.toValuationSubring) :
    ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P →
      μ (Q.evalAt T - P.evalAt T) = μ (Q.evalAt ρ - P.evalAt ρ) := by sorry
