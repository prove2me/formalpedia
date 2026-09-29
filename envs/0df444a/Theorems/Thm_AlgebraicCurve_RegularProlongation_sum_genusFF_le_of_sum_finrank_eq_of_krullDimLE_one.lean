-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
-- name    : AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2f7d5644-13f5-5e83-b62a-47e8bc3db2a1
-- title:
--   Deuring's genus inequality for a complete family of prolongations
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, let $A \subseteq L$ be a valuation subring whose Krull dimension is at most $1$, and write $k =$ `IsLocalRing.ResidueField A` for its residue field. Let $F$ be a field extension of $L$, let $\iota$ be a finite index type, and for each $i$ let $\bar F_i$ be a field equipped with a $k$-algebra structure together with a term `R i` of the structure `RegularProlongation A F (Fb i)`: that is, a valuation subring $\mathcal{O}_i$ of $F$ and a ring homomorphism $\mathrm{res}_i \colon \mathcal{O}_i \to \bar F_i$ such that for $x \in L$ one has $x \in \mathcal{O}_i$ exactly when $x \in A$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal{O}_i$, $\mathrm{res}_i$ restricted to $A$ is the residue map of $A$ followed by $k \to \bar F_i$, and every nonzero $u \in F$ admits $c \in L$ with $c u \in \mathcal{O}_i$ and $\mathrm{res}_i(cu) \neq 0$. Assume the map $i \mapsto \mathcal{O}_i$ is injective, that $f \in F$ lies in every $\mathcal{O}_i$, that $f$ is transcendental over $L$, that $F$ is finite-dimensional over the intermediate field $L(f)$, that each residue $\bar f_i = \mathrm{res}_i(f)$ is transcendental over $k$, and that $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Then $\sum_i \mathrm{genusFF}(k, \bar F_i) \le \mathrm{genusFF}(L, F)$, where $\mathrm{genusFF}(K,E)$ denotes the $K$-dimension of $H^1$ of the repartition complex at the zero divisor of $E/K$.
--
--   This is Deuring's inequality bounding the sum of the genera of the residue function fields of a complete family of prolongations of a valuation by the genus of the function field upstairs, here in the case of a valuation of rank at most one, which is the case relevant to valuation subrings of $\overline{\mathbb{Q}}$. It is used in the comparison of genera of modular curves in characteristic $0$ and in reduction, and in the construction of good constant reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
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
