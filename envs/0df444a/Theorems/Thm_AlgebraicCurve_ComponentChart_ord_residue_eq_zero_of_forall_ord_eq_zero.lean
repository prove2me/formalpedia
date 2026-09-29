-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero
-- name    : AlgebraicCurve.ComponentChart.ord_residue_eq_zero_of_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f94b9640-3f3f-53b8-902c-36a5440b7b2e
-- title:
--   ord_Q of a reduction vanishes above a zero-free class
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, let $F$ be a field that is an $L$-algebra satisfying `HasPrincipalDivisors L F` (every non-zero $f \in F$ admits a finitely supported divisor $D$ on the places of $F/L$ with $D(v) = v.\mathrm{ord}(f)$ for all $v$ and $\deg D = 0$), and let $\bar F$ be a field that is an algebra over the residue field of $A$. Here a place of $F/L$ is a valuation subring of $F$ containing the image of $L$, distinct from $F$ itself, and with principal ideals, and $v.\mathrm{ord}(f)$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. Let $C$ be a component chart of $F$ over $A$ with values in $\bar F$, consisting of a valuation subring $C.\mathrm{integers}$ of $F$, a surjective ring homomorphism $C.\mathrm{residue}$ onto $\bar F$ with kernel the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$, a finite set $C.\mathrm{nodes}$ of places of $\bar F$ over the residue field of $A$, and a map $C.\mathrm{placeMap}$ on places, subject to the compatibility axioms of `ComponentChart` (including the pushforward identity `mapDomain_placeMap`). Let $f \in C.\mathrm{integers}$ have non-zero reduction $\bar f = C.\mathrm{residue}(f)$, and let $Q$ be a place of $\bar F$ over the residue field of $A$ with $Q \notin C.\mathrm{nodes}$. If $P.\mathrm{ord}(f) = 0$ for every $P \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}(P) = Q$, then $Q.\mathrm{ord}(\bar f) = 0$.
--
--   This records that a chart function whose reduction is non-zero and which has neither zero nor pole at any place of the chart domain lying over a non-nodal point $Q$ reduces to a function that is a unit at $Q$. It is used in the construction of sections with prescribed integrality on semistable models, namely in [`AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel`](thm.html#AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_balanced_of_semistableModel) and [`AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel`](thm.html#AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_residue_eq_zero_of_forall_ord_eq_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes)
    (hord : ∀ P ∈ C.dom, C.placeMap P = Q → P.ord f = 0) :
    Q.ord (C.residue ⟨f, hf⟩) = 0 := by sorry
