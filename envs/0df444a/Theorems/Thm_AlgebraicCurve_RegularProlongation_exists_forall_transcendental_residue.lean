-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_transcendental_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/72e6fe17-600e-54cc-87c8-6c74aa9cac35
-- title:
--   Simultaneously good transcendental element for several regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ which is assumed to admit an element $x$ transcendental over $L$ such that $F$ is finite-dimensional over the intermediate field $L(x)$. Let $\iota$ be a finite index type and, for each $i$, let $F_i$ be a field equipped with an algebra structure over the residue field $k = A/\mathfrak{m}_A$, together with a term $R_i$ of `RegularProlongation A F (F_i)`: that is, a valuation subring $\mathcal{O}_i \subseteq F$ and a ring homomorphism $\mathrm{res}_i \colon \mathcal{O}_i \to F_i$ such that an element of $L$ lies in $A$ exactly when its image in $F$ lies in $\mathcal{O}_i$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal{O}_i$, $\mathrm{res}_i$ restricted to $A$ is the residue map of $A$ followed by $k \to F_i$, and every nonzero $f \in F$ has a scaling $c \cdot f$ ($c \in L$) lying in $\mathcal{O}_i$ with nonzero residue. Assume the assignment $i \mapsto \mathcal{O}_i$ is injective, and that no $F_i$ is algebraic over $k$. Then there is $f \in F$ together with a witness that $f \in \mathcal{O}_i$ for all $i$, such that $f$ is transcendental over $L$, $F$ is finite-dimensional over $L(f)$, and for each $i$ the residue $\mathrm{res}_i(f)$ is transcendental over $k$.
--
--   This is the construction of a simultaneously good transcendental element in the Deuring–Lamprecht treatment of constant reduction of one-variable function fields: once such an $f$ is available, each residue field $F_i$ is a one-variable function field over $k(\mathrm{res}_i(f))$ and the fundamental inequality between $[F:L(f)]$ and the degrees $[F_i : k(\mathrm{res}_i(f))]$ becomes applicable. The proof uses only the simultaneous approximation statement [`ValuationSubring.exists_forall_mem_and_sub_mem_nonunits`](thm.html#ValuationSubring.exists_forall_mem_and_sub_mem_nonunits) for a family of pairwise incomparable valuation subrings, and the result feeds into [`AlgebraicCurve.RegularProlongation.isCurveOver_and_essFiniteType_of_exists_transcendental`](thm.html#AlgebraicCurve.RegularProlongation.isCurveOver_and_essFiniteType_of_exists_transcendental).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (hnA : ∀ i, ¬ Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (Fb i)) :
    ∃ f : F, ∃ hf : ∀ i, f ∈ (R i).integers,
      Transcendental L f ∧
      FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F ∧
      ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩) := by sorry
