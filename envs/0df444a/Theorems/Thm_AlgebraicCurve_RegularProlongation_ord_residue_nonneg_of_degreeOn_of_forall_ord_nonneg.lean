-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
-- name    : AlgebraicCurve.RegularProlongation.ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0c804442-182e-5a08-85e7-893e962af0f2
-- title:
--   Nonnegative ord_Q of a reduction from effectivity on D
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, $F$ a field which is an $L$-algebra, and $\bar F$ a field which is an algebra over the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$, that is, a valuation subring $R.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $R.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, inducing $A$ on $L$ and compatible with reduction on $A$, and such that every non-zero element of $F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with non-zero reduction. Let $Q$ be a place of $\bar F$ over the residue field of $A$ (a proper valuation subring containing the base field whose associated local ring is a principal ideal ring), and let $D$ be a set of places of $F$ over $L$. Assume the degree compatibility $R.\mathrm{DegreeOn}\,Q\,D$: for every $g\in R.\mathrm{integers}$ with $R.\mathrm{residue}\,g\neq 0$ and every finitely supported $D':\mathrm{Place}\,L\,F\to\mathbb Z$ with $D'(P)=\operatorname{ord}_P(g)$ for $P\in D$ and $D'(P)=0$ for $P\notin D$, the total sum $\sum_P D'(P)$ equals $\operatorname{ord}_Q(R.\mathrm{residue}\,g)$. Let $f\in R.\mathrm{integers}$ satisfy $R.\mathrm{residue}\,f\neq 0$, let the set of places $P$ of $F/L$ with $\operatorname{ord}_P(f)\neq 0$ be finite, and let $\operatorname{ord}_P(f)\geq 0$ for all $P\in D$. Then $0\leq\operatorname{ord}_Q(R.\mathrm{residue}\,f)$.
--
--   This records the elementary consequence of the degree compatibility between a regular prolongation and a place $Q$ of the reduced field: a function integral on $R$ with non-zero reduction and no pole along the places of $D$ reduces to a function with no pole at $Q$. It is used in the analysis of the residue discs and node directions of modular curves at full level, where it rules out a pole of the reduction of a rescaled Hasse-type function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField A) Fbar) (D : Set (Place L F))
    (hdeg : R.DegreeOn Q D)
    (f : R.integers) (hres : R.residue f ≠ 0)

    (hfin : {P : Place L F | P.ord (f : F) ≠ 0}.Finite)

    (hD : ∀ P ∈ D, 0 ≤ P.ord (f : F)) :
    0 ≤ Q.ord (R.residue f) := by sorry
