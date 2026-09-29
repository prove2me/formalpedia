-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/1eaecc40-50c9-5763-a5d0-104ddc3dc647
-- title:
--   Connectedness of constant reduction over a rank-one valuation ring
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, let $A \subseteq L$ be a valuation subring whose ring-theoretic Krull dimension is at most $1$, and write $k = \mathrm{ResidueField}\,A$ for its residue field. Let $F$ be a field extension of $L$, let $\iota$ be a finite index type, and for each $i$ let $Fb\ i$ be a field equipped with a $k$-algebra structure together with a `RegularProlongation` $R\ i$ of $A$ to $F$ with residue field $Fb\ i$: that is, a valuation subring $(R\ i).\mathrm{integers}$ of $F$, and a ring homomorphism $(R\ i).\mathrm{residue}$ from it onto $Fb\ i$ whose kernel is the maximal ideal, such that an element of $L$ lies in $(R\ i).\mathrm{integers}$ exactly when it lies in $A$, the residue map extends the residue map of $A$ along $k \to Fb\ i$, and every nonzero $x \in F$ admits $c \in L$ with $c \cdot x$ in $(R\ i).\mathrm{integers}$ and nonzero residue. Assume the valuation subrings $(R\ i).\mathrm{integers}$ are pairwise distinct, i.e. $i \mapsto (R\ i).\mathrm{integers}$ is injective. Let $f \in F$ lie in every $(R\ i).\mathrm{integers}$, be transcendental over $L$, with $F$ finite-dimensional over the intermediate field $L(f)$; assume each residue $\bar f_i = (R\ i).\mathrm{residue}\,f$ is transcendental over $k$ and that $\sum_i [Fb\ i : k(\bar f_i)] = [F : L(f)]$. Finally let $h = (h_i)_i \in \prod_i Fb\ i$ belong to both of the following $k$-submodules of $\prod_i Fb\ i$: the $k$-span of the joint residue vectors $((R\ i).\mathrm{residue}\,u)_i$ of those $u \in F$ lying in all $(R\ i).\mathrm{integers}$ and in every valuation subring $V$ of $F$ containing the image of $L$ and containing $f$, and the $k$-span of the same vectors for those $u$ subject instead to lying in every such $V$ containing $f^{-1}$. Then $h$ is constant and defined over $k$: there exists $c \in k$ with $h_i = \mathrm{algebraMap}\,k\,(Fb\ i)\,c$ for every $i$.
--
--   This is the connectedness theorem for constant reductions (Roquette's Zusammenhangssatz) in the case of a valuation ring of rank at most one: the two spans are the coordinate rings of the two affine charts of the special fibre of the $f$-model of $F$ over $A$, and the conclusion says that the global sections of the structure sheaf of that special fibre reduce to $k$. It is cited in the proof of the bound on the sum of the genera of the residue function fields $Fb\ i$ for a complete family of regular prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
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
