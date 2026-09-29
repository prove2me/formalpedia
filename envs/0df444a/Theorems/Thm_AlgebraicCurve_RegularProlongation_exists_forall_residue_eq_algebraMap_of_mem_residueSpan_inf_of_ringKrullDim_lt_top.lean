-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/11800097-3ddf-5791-ba52-50c4071a2312
-- title:
--   Constant reduction: joint residues regular on both charts are diagonal
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring whose Krull dimension is finite ($\mathrm{ringKrullDim}\,A < \top$), with residue field $k = \mathrm{ResidueField}\,A$. Let $F$ be a field extension of $L$, let $\iota$ be a finite index type, and for each $i$ let $\bar F_i$ be a field that is an algebra over $k$, together with a regular prolongation $R_i$ of $A$ to $F$ with residue field $\bar F_i$: that is, a valuation subring $(R_i).\mathrm{integers} \subseteq F$ and a ring homomorphism $(R_i).\mathrm{residue}$ from it onto $\bar F_i$ whose kernel is the maximal ideal, such that for $x \in L$ one has $x \in A$ iff its image lies in $(R_i).\mathrm{integers}$, such that the residue map restricted to $A$ is the residue map of $A$ followed by the structure map $k \to \bar F_i$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $(R_i).\mathrm{integers}$ with nonzero residue. Assume the valuation subrings $(R_i).\mathrm{integers}$ are pairwise distinct (the map $i \mapsto (R_i).\mathrm{integers}$ is injective). Let $f \in F$ lie in all $(R_i).\mathrm{integers}$, be transcendental over $L$, with $F$ finite-dimensional over the intermediate field $L(f) = \mathrm{adjoin}\,L\,\{f\}$, let each residue $\bar f_i = (R_i).\mathrm{residue}\,f$ be transcendental over $k$, and assume the degree equality $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Finally let $h \in \prod_i \bar F_i$ belong to the $k$-span of the set of vectors of residues $((R_i).\mathrm{residue}\,u)_i$ of elements $u \in F$ lying in all $(R_i).\mathrm{integers}$ and in every valuation subring of $F$ containing $\mathrm{image}(L)$ and $f$, and also to the corresponding $k$-span formed with $f^{-1}$ in place of $f$. Then there is $c \in k$ with $h_i =$ the image of $c$ in $\bar F_i$ for every $i$.
--
--   This is the connectedness theorem for constant reductions (Roquette's Zusammenhangssatz) in the form $H^0$ of the reduced special fibre of the normalised $f$-model equals the residue field $k$: a vector of residues that is regular on both the $f$-chart and the $f^{-1}$-chart is a diagonal constant. The finite-rank hypothesis on $A$ is used through the finiteness of $\mathrm{Spec}\,A$ and the computation of Krull dimensions of residue valuation subrings of intervals of primes; it feeds the version over an arbitrary algebraically closed valued field, [`AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (hA : ringKrullDim A < ⊤)
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
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∃ c : IsLocalRing.ResidueField A, ∀ i, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by sorry
