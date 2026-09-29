-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/fa0da7eb-e3d1-51d1-b156-8455c9bbdfbc
-- title:
--   Joint residue image of V has k-dimension dim_L V
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $\bar F_i$ be a field that is a $k$-algebra, and let $R_i$ be a regular prolongation of $A$ to $F$ with values in $\bar F_i$: that is, a valuation subring $\mathcal O_i \subseteq F$ together with a ring homomorphism $\mathrm{res}_i \colon \mathcal O_i \to \bar F_i$ such that $x \in A \iff$ the image of $x$ in $F$ lies in $\mathcal O_i$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal O_i$, $\mathrm{res}_i$ agrees on $A$ with $A \to k \to \bar F_i$, and every nonzero $f \in F$ admits $c \in L$ with $c f \in \mathcal O_i$ and $\mathrm{res}_i(c f) \neq 0$. Assume the map $i \mapsto \mathcal O_i$ is injective; let $f \in F$ lie in every $\mathcal O_i$, with $\bar f_i = \mathrm{res}_i(f)$ transcendental over $k$ for every $i$; assume $F$ is finite-dimensional over the intermediate field $L(f)$ and that the family is defectless in the sense $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Then for every finite-dimensional $L$-subspace $V \subseteq F$, the $k$-span inside $\prod_i \bar F_i$ of the set of tuples $(h_i)_i$ for which there exists $u \in V$ lying in all $\mathcal O_i$ with $\mathrm{res}_i(u) = h_i$ for every $i$ has $k$-dimension equal to $\dim_L V$.
--
--   This is the dimension-preservation statement for constant reduction along a complete, defectless family of prolongations, in the joint form: the $k$-span of the image of $V \cap \bigcap_i \mathcal O_i$ under the simultaneous residue map into $\prod_i \bar F_i$ has the same dimension as $V$. It underlies the construction of bases of $V$ with linearly independent joint residues and the resulting genus inequalities for the residue function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
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
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) =
      Module.finrank L V := by sorry
