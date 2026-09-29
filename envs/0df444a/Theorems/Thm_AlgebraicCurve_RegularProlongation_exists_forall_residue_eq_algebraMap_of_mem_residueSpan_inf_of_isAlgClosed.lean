-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/fef36fcb-c584-59a6-9f42-1b187aa43269
-- title:
--   Constants of a complete family of regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k = \mathrm{ResidueField}\,A$, and $F$ a field extension of $L$. Let $\iota$ be a finite index set and, for each $i$, let $\bar F_i$ be a field extension of $k$ and $R_i$ a `RegularProlongation` of $A$ to $F$ with values in $\bar F_i$: that is, a valuation subring $\mathcal O_i = (R_i).integers$ of $F$ together with a ring homomorphism $(R_i).residue \colon \mathcal O_i \to \bar F_i$ such that for $x \in L$ one has $x \in A$ iff its image in $F$ lies in $\mathcal O_i$, the residue map is surjective with kernel the maximal ideal of $\mathcal O_i$, it agrees on $A$ with the structural map $k \to \bar F_i$ composed with the residue map of $A$, and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O_i$ of nonzero residue. Assume the map $i \mapsto \mathcal O_i$ is injective. Let $f \in F$ lie in every $\mathcal O_i$, be transcendental over $L$ with $F$ finite-dimensional over $L(f)$, have each residue $\bar f_i = (R_i).residue(f)$ transcendental over $k$, and satisfy the completeness relation $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Let $h = (h_i)_i \in \prod_i \bar F_i$ lie in both of the following $k$-submodules of $\prod_i \bar F_i$: the $k$-span of the joint residue vectors $((R_i).residue(u))_i$ of those $u \in \bigcap_i \mathcal O_i$ lying in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$, and the $k$-span of the corresponding vectors for those $u$ lying in every valuation subring containing the image of $L$ and containing $f^{-1}$. Then there is $c \in k$ with $h_i =$ the image of $c$ in $\bar F_i$ for every $i$.
--
--   This is the statement that the constant reduction attached to a complete family of regular prolongations is connected, in the form $H^0 = k$: the intersection of the $k$-spans of the residues of the integral closures of $L[f]$ and of $L[f^{-1}]$ consists of the diagonal constants, with no restriction on the characteristic of $L$. It feeds the genus inequality for complete families of regular prolongations, [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_isAlgClosed
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
