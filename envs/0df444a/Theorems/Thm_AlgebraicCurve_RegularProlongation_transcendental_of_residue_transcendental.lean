-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental
-- name    : AlgebraicCurve.RegularProlongation.transcendental_of_residue_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2b0ce125-035e-52fe-bf85-f5b2757d79d8
-- title:
--   Transcendence lifts from the residue field of a regular prolongation
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field $\kappa(A)$ of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with residue field $\bar F$, that is: a valuation subring $\mathcal{O} = R.\mathrm{integers}$ of $F$ together with a ring homomorphism $\mathrm{res} \colon \mathcal{O} \to \bar F$ such that for $x \in L$ one has $x \in A$ if and only if the image of $x$ in $F$ lies in $\mathcal{O}$; $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal{O}$; for every $a \in A$ the element $\mathrm{res}$ of the image of $a$ in $\mathcal{O}$ equals the image of the residue of $a$ under $\kappa(A) \to \bar F$; and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal{O}$ and $\mathrm{res}(c \cdot f) \neq 0$. Let $x \in \mathcal{O}$ be such that $\mathrm{res}(x)$ is transcendental over $\kappa(A)$. Then the image of $x$ in $F$ is transcendental over $L$.
--
--   This is the transcendence half of the dictionary between a place of a function field and its residue extension: residual transcendence forces transcendence upstairs. It is used in the study of integral elements over a regular prolongation, for instance in [`AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers`](thm.html#AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers), in [`AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring`](thm.html#AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring) and in the construction of prolongations to intermediate fields with prescribed residue degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.transcendental_of_residue_transcendental
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x)) :
    Transcendental L (x : F) := by sorry
