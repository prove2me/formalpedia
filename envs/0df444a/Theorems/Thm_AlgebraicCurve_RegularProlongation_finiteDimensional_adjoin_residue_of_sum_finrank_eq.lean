-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/af25028a-e1c5-585d-8b5d-9c8069cabd72
-- title:
--   Finiteness of each residue extension over k(̄ fᵢ)
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k = \mathrm{ResidueField}\,A$, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $\bar F_i$ be a field equipped with a $k$-algebra structure, together with a regular prolongation $R_i$ of $A$ to $F$ with residue field $\bar F_i$: that is, a valuation subring $\mathcal{O}_i = (R_i).\mathrm{integers}$ of $F$ and a ring homomorphism $\mathrm{res}_i : \mathcal{O}_i \to \bar F_i$ such that for $x \in L$ one has $x \cdot 1_F \in \mathcal{O}_i$ exactly when $x \in A$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal{O}_i$, $\mathrm{res}_i$ restricted to $A$ agrees with $A \to k \to \bar F_i$, and every nonzero $f \in F$ admits $c \in L$ with $c f \in \mathcal{O}_i$ and $\mathrm{res}_i(c f) \neq 0$. Assume the subrings $\mathcal{O}_i$ are pairwise distinct (the map $i \mapsto (R_i).\mathrm{integers}$ is injective), and let $f \in F$ lie in every $\mathcal{O}_i$ and have residue $\bar f_i = \mathrm{res}_i(f)$ transcendental over $k$ for every $i$, with $F$ finite over the intermediate field $L(f)$. Assume furthermore $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Then, for a given index $i$, $\bar F_i$ is finite-dimensional over $k(\bar f_i)$.
--
--   This supplies, in the setting of a family of regular prolongations of a valuation of $L$ to a finite extension $F$ of $L(f)$ with transcendental residues, the finiteness instance $[\bar F_i : k(\bar f_i)] < \infty$, so that each reduction $\bar F_i$ is a function field of one variable over $k$ with generator $\bar f_i$. It is used by the results on Gauss bases and on bounds for $\sum_i$ of ranks of residue spans in the reduction theory of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i : ι) :
    FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := by sorry
