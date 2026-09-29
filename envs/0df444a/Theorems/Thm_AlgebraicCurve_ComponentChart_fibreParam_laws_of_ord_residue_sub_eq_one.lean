-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_fibreParam_laws_of_ord_residue_sub_eq_one
-- name    : AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f72b9d45-a041-53ee-8b6d-bf5fa7ba1e65
-- title:
--   Fibre coordinate from a reduction of order one
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring with residue field $k$, and $F$ a field extension of $L$ in which every nonzero element admits a finitely supported divisor of degree zero recording its orders at all places (`HasPrincipalDivisors`), where a place of $F/L$ is a proper valuation subring of $F$ containing $L$ whose ring is a principal ideal ring, and $\operatorname{ord}$ is minus the logarithm of the associated adic valuation. Let $\bar F$ be a field over $k$ and $C$ a component chart for $A$, $F$, $\bar F$, with valuation ring $C.\mathrm{integers}\subseteq F$, surjective residue map to $\bar F$ with kernel the maximal ideal, a domain $C.\mathrm{dom}$ of places of $F/L$, a finite set of nodes, and a reduction map $C.\mathrm{placeMap}$ on places, subject to the chart axioms. Let $P\in C.\mathrm{dom}$ be rational (the structure map $L\to P$'s residue field is surjective), assume $x:=C.\mathrm{placeMap}\,P$ is likewise rational over $k$, and let $T\in C.\mathrm{integers}$ lie in the valuation ring of every $w\in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,w=x$. Write $\bar T$ for the residue of $T$ and assume $\operatorname{ord}_x\bigl(\bar T-\mathrm{evalAt}_x(\bar T)\bigr)=1$, the value being pushed from $k$ to $\bar F$. Then $t:=T-\mathrm{evalAt}_P(T)$ (image in $F$) lies in $C.\mathrm{integers}$, its residue is nonzero with $\operatorname{ord}_x$ equal to $1$, $\operatorname{ord}_P(t)>0$, and $\operatorname{ord}_Q(t)=0$ for every $Q\in C.\mathrm{dom}$, $Q\neq P$, with $C.\mathrm{placeMap}\,Q=x$.
--
--   The statement produces a local coordinate on the residue disc of a rational place $P$ of a component chart: a chart-integral function vanishing simply at $P$, with no other zero in the fibre of $C.\mathrm{placeMap}$ over the reduction $x$, and whose reduction is a uniformiser at $x$. It is used in the construction of fibre coordinates for prolongation pairs of place specialisations on modular curves, via [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_fibreParam_laws_of_ord_residue_sub_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (P : Place L F) (hP : P ∈ C.dom) (hPrat : P.IsRational)
    (hxrat : (C.placeMap P).IsRational) (T : F) (hT : T ∈ C.integers)
    (hreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T ∈ w.toValuationSubring)
    (hunif : (C.placeMap P).ord (C.residue ⟨T, hT⟩
        - algebraMap (IsLocalRing.ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨T, hT⟩))) = 1) :
    ∃ h : T - algebraMap L F (P.evalAt T) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap P).ord (C.residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (T - algebraMap L F (P.evalAt T)) ∧
      ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ P → Q.ord (T - algebraMap L F (P.evalAt T)) = 0 := by sorry
