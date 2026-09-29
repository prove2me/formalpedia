-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one
-- name    : AlgebraicCurve.ComponentChart.ord_eq_of_fibre_of_ord_residue_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7c0d22e0-16dd-527e-b973-0d2710da0b47
-- title:
--   Simple zero on the reduction forces a unique simple zero on the fibre
-- statement:
--   Let $L$ be a field, $A$ a valuation subring of $L$, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field of $A$, and assume $F/L$ has principal divisors, i.e. every $f \in F^{\times}$ admits a finitely supported divisor $D$ on the places of $F/L$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$ (a place being a valuation subring of $F$ containing $L$, different from $F$ and a principal ideal ring, with $\operatorname{ord}_v = -\log$ of the associated $\mathbb{Z}^{m0}$-valued adic valuation). Let $C$ be a component chart: a valuation subring $C.\mathrm{integers}$ of $F$ with a surjective reduction map $C.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$, a finite set $C.\mathrm{nodes}$ of places of $\bar F$ over the residue field of $A$, a reduction map $C.\mathrm{placeMap}$ on places, and the chart axioms, among them the compatibility asserting that for a chart-integral $g$ with nonzero reduction and any divisor supported on $C.\mathrm{dom}$ computing $\operatorname{ord}$ there, the pushforward along $C.\mathrm{placeMap}$ has coefficient $\operatorname{ord}_Q$ of the reduction of $g$ at every non-node $Q$. Let $f \in C.\mathrm{integers}$ have nonzero reduction $\bar f$, let $P \in C.\mathrm{dom}$ satisfy $\operatorname{ord}_{C.\mathrm{placeMap}(P)}(\bar f) = 1$, suppose $f$ lies in the valuation subring of every $w \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}(w) = C.\mathrm{placeMap}(P)$, and suppose $\operatorname{ord}_P(f) > 0$. Then $\operatorname{ord}_P(f) = 1$, and $\operatorname{ord}_w(f) = 0$ for every $w \in C.\mathrm{dom}$, $w \neq P$, with $C.\mathrm{placeMap}(w) = C.\mathrm{placeMap}(P)$.
--
--   This is the specialisation statement for divisors on a component chart: a chart-integral function whose reduction has a simple zero at a non-nodal point of the reduction, and which is regular along the whole fibre over that point, has a single simple zero on that fibre. It is used in the construction of fibre parameters for charts, via [`AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one`](thm.html#AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_eq_of_fibre_of_ord_residue_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (P : Place L F) (hP : P ∈ C.dom) (hord : (C.placeMap P).ord (C.residue ⟨f, hf⟩) = 1)
    (hreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f ∈ w.toValuationSubring)
    (hPz : 0 < P.ord f) :
    P.ord f = 1 ∧ ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → w ≠ P → w.ord f = 0 := by sorry
