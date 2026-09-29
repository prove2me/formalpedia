-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/f5314b1c-354f-5444-8745-c1b0e01296e8
-- title:
--   Zero joint residue forces division by a non-unit of A
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $F_i$ be a field equipped with a $k$-algebra structure, and let $R_i$ be a regular prolongation of $A$ to $F$ with residue field $F_i$: a valuation subring $\mathcal O_i =$ `(R i).integers` of $F$ together with a surjective ring homomorphism $\mathrm{res}_i : \mathcal O_i \to F_i$ whose kernel is the maximal ideal of $\mathcal O_i$, such that the structure map $L \to F$ pulls $\mathcal O_i$ back to exactly $A$ (i.e. $x \in A$ iff the image of $x$ lies in $\mathcal O_i$), such that $\mathrm{res}_i$ restricted to $A$ is the structure map $k \to F_i$ composed with reduction, and such that every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O_i$ and $\mathrm{res}_i(c\cdot f) \neq 0$. Assume the $\mathcal O_i$ are pairwise distinct (the map $i \mapsto \mathcal O_i$ is injective). Let $f \in F$ lie in every $\mathcal O_i$, with each residue $\mathrm{res}_i(f)$ transcendental over $k$, let $F$ be finite-dimensional over the intermediate field $L(f)$, and assume the equality $\sum_i [F_i : k(\mathrm{res}_i(f))] = [F : L(f)]$ of finite ranks. Finally let $V$ be an $L$-subspace of $F$ of finite dimension, and let $u \in F$ lie in $V$ and in every $\mathcal O_i$ with $\mathrm{res}_i(u) = 0$ for all $i$. Then there exist $a \in A$ which is not a unit of $A$ and $u' \in F$ lying in $V$ and in every $\mathcal O_i$, such that $u = a \cdot u'$ (the image of $a$ in $L$ acting on $F$).
--
--   This is the non-trivial inclusion in the identification of the kernel of the joint residue map $V \cap \bigcap_i \mathcal O_i \to \prod_i F_i$ with $\mathfrak m_A \cdot (V \cap \bigcap_i \mathcal O_i)$, in the defectless situation of constant reduction of function fields studied by Deuring and Roquette, where the prolongations $R_i$ of $A$ and the transcendental element $f$ satisfy the fundamental rank equality. It rests on the existence of a basis of $F$ over $L(f)$ contained in the $\mathcal O_i$ whose joint residues are linearly independent, and is used in the construction of Gauss bases and in the analysis of residue spans for rings of Krull dimension at most one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
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
    (V : Submodule L F) [FiniteDimensional L V]
    (u : F) (huO : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, huO i⟩ = 0) :
    ∃ (a : A) (u' : F), ¬ IsUnit a ∧ (∀ i, u' ∈ (R i).integers) ∧ u' ∈ V ∧
      u = (a : L) • u' := by sorry
