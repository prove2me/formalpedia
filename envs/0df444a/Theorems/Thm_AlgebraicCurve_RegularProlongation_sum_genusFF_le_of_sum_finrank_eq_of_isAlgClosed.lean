-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
-- name    : AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/aec27f42-5f81-5af2-a675-0b0ddc882104
-- title:
--   Deuring's genus inequality for defectless families of regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k = \mathrm{ResidueField}(A)$, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $\bar F_i$ be a field extension of $k$ together with a regular prolongation $R_i$ of $A$ to $F$ with residue field $\bar F_i$: that is, a valuation subring $\mathcal{O}_i \subseteq F$ and a ring homomorphism $\mathcal{O}_i \to \bar F_i$ which is surjective, has kernel exactly the maximal ideal of $\mathcal{O}_i$, satisfies $\mathcal{O}_i \cap L = A$ in the sense that $x \in L$ lies in $A$ iff its image in $F$ lies in $\mathcal{O}_i$, is compatible with the residue map of $A$ over $k$, and is such that every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal{O}_i$ of nonzero residue. Assume the assignment $i \mapsto \mathcal{O}_i$ is injective. Let $f \in F$ lie in every $\mathcal{O}_i$, be transcendental over $L$, have $F$ finite-dimensional over $L(f)$, have each residue $\bar f_i \in \bar F_i$ transcendental over $k$, and satisfy $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Then $\sum_i g(\bar F_i/k) \le g(F/L)$, where the genus $g$ of a function field is the dimension over the constant field of the first cohomology group $H^1$ of the zero divisor.
--
--   This is Deuring's genus inequality for the complete and defectless family of prolongations of the Gauss valuation determined by $f$, here in arbitrary characteristic since only algebraic closedness of $L$ is assumed. It feeds the study of reduction of function fields, being used in the proof that a residue which is a $p$-th power is the residue of a $p$-th power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F := by sorry
