-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/4f81776e-3541-5bb8-addc-70955be212b9
-- title:
--   A defectless family of prolongations exhausts all extensions
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$. Let $\iota$ be a finite nonempty index type and, for each $i$, let $Fb\,i$ be a field equipped with an algebra structure over the residue field $k$ of $A$, and let $R\,i$ be a regular prolongation of $A$ to $F$ with residue field $Fb\,i$: that is, a valuation subring $(R\,i).\mathrm{integers}$ of $F$ together with a ring homomorphism $(R\,i).\mathrm{residue}$ onto $Fb\,i$ whose kernel is the maximal ideal of that valuation subring, such that an element of $L$ lies in $A$ exactly when its image in $F$ lies in $(R\,i).\mathrm{integers}$, the residue map restricted to $A$ agrees with $A \to k \to Fb\,i$, and every nonzero $f \in F$ can be scaled by some $c \in L$ so that $c \cdot f$ is integral with nonzero residue. Assume the valuation subrings $(R\,i).\mathrm{integers}$ are pairwise distinct, i.e. $i \mapsto (R\,i).\mathrm{integers}$ is injective. Let $f \in F$ lie in $(R\,i).\mathrm{integers}$ for every $i$, with residue in $Fb\,i$ transcendental over $k$ for every $i$, let $F$ be finite-dimensional over the intermediate field $L(f)$, and assume the fundamental inequality is an equality: $\sum_i [\,Fb\,i : k(\overline{f}_i)\,] = [F : L(f)]$, where $\overline{f}_i$ denotes the residue of $f$ in $Fb\,i$. Then for every index $i_0$ and every valuation subring $V$ of $F$ such that an element $e \in L(f)$ lies in $V$ if and only if it lies in $(R\,i_0).\mathrm{integers}$, there is an index $j$ with $V = (R\,j).\mathrm{integers}$.
--
--   This is the completeness assertion for a defectless family of regular prolongations: once the sum of the residual degrees over $k(\overline{f}_i)$ matches $[F:L(f)]$, the rings $(R\,i).\mathrm{integers}$ form the complete list of valuation subrings of $F$ whose trace on $L(f)$ is the common Gauss ring. It is used in the analysis of the reduction of the modular curve model, where it supplies the exhaustiveness hypothesis needed to control integrality of elements of $\bigcap_i (R\,i).\mathrm{integers}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i₀ : ι) (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i₀).integers)) :
    ∃ j, V = (R j).integers := by sorry
