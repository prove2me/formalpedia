-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf
-- name    : AlgebraicCurve.RegularProlongation.span_residue_lSpace_le_residueSpan_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e861a5cc-d70f-501a-a726-1ae1eb8b6310
-- title:
--   Residues of L(M· D) lie in both chart spans
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $\bar F_i$ be a field that is a $k$-algebra, together with a regular prolongation $R_i$ of $A$ to $F$ with values in $\bar F_i$: a valuation subring $\mathcal O_i = (R_i).\mathrm{integers}$ of $F$ and a surjective ring homomorphism $\mathcal O_i \to \bar F_i$ whose kernel is the maximal ideal of $\mathcal O_i$, contracting to $A$ on $L$ and compatible with $A \to k$, and such that every nonzero element of $F$ has an $L$-multiple in $\mathcal O_i$ with nonzero residue. Let $f \in F$ lie in each $\mathcal O_i$, assume $F$ is finite-dimensional over the intermediate field $L(f)$, let $D$ be a divisor of $F/L$ (a finitely supported integer-valued function on the places of $F/L$, a place being a proper valuation subring of $F$ containing $L$ whose valuation ring is a principal ideal ring) with $D(v) = \max(0, -\operatorname{ord}_v f)$ for every place $v$, and let $M$ be a natural number. For a subset of $F$, form the $k$-submodule of $\prod_i \bar F_i$ spanned by the tuples of residues $((R_i).\mathrm{residue}\,u)_i$ of those $u$ in the subset lying in all $\mathcal O_i$. The assertion is that the span attached to $\{u : \forall v,\ v(u) \le \exp((M\cdot D)(v))\}$, i.e. to the Riemann–Roch space $L(M\cdot D)$, is contained in the intersection of the span attached to $\{u : u \in V$ for every valuation subring $V$ of $F$ containing $L$ with $f \in V\}$ and the span attached to $\{u : u\,(f^M)^{-1} \in V$ for every valuation subring $V$ of $F$ containing $L$ with $f^{-1} \in V\}$.
--
--   With $D$ the pole divisor of $f$, this says that the residues of the Riemann–Roch space $L(M\cdot D)$ are captured simultaneously by the two affine charts determined by $f$ and by $f^{-1}$ (the latter twisted by $f^{M}$), the containment already holding elementwise in $F$. It is the first step in the comparison of $\ell_F(M D)$ with the dimensions of the residual Riemann–Roch spaces, used in [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed) and [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.span_residue_lSpace_le_residueSpan_inf
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (M : ℕ) :
    Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ LSpace (M • D) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ≤
      Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
              u * (f ^ M)⁻¹ ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by sorry
