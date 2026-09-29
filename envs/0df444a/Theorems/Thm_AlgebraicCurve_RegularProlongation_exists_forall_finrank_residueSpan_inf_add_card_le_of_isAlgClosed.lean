-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e25a4f98-7e80-541e-9ad9-f7689ba6d7ad
-- title:
--   Eventual dimension count for residue spans of regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $\bar F_i$ be a field extension of $k$ and $R_i$ a regular prolongation of $A$ to $F$ with values in $\bar F_i$: that is, a valuation subring $\mathcal O_i = (R_i).\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $\mathcal O_i \to \bar F_i$ whose kernel is the maximal ideal of $\mathcal O_i$, such that $\operatorname{alg}_{L\to F}(x) \in \mathcal O_i$ exactly when $x \in A$, the homomorphism is compatible with $A \to k$ on elements of $A$, and every non-zero $f \in F$ has an $L$-multiple lying in $\mathcal O_i$ with non-zero residue. Assume the map $i \mapsto \mathcal O_i$ is injective. Let $f \in \bigcap_i \mathcal O_i$ be transcendental over $L$ with $F$ finite-dimensional over $L(f)$, assume each residue $\bar f_i$ is transcendental over $k$, and assume $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. For each $i$ let $\bar D_i$ be the divisor on $\bar F_i/k$ (a finitely supported integer-valued function on the places of $\bar F_i$ over $k$, places being the proper valuation subrings containing $k$ that are principal ideal rings) given by $\bar D_i(w) = \max(0, -\operatorname{ord}_w \bar f_i)$. Write, for $M \in \mathbb N$, $P$ for the $k$-span inside $\prod_i \bar F_i$ of the joint residue tuples $(\bar u_i)_i$ of those $u \in \bigcap_i \mathcal O_i$ lying in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$, and $P'_M$ for the $k$-span of the joint residue tuples of those $u \in \bigcap_i \mathcal O_i$ with $u (f^M)^{-1} \in V$ for every valuation subring $V$ of $F$ containing the image of $L$ and containing $f^{-1}$; likewise $P'$ for the span attached to the condition $u \in V$ for all such $V$. The conclusion is that there exists $M_0$ such that for every $M \ge M_0$ the $k$-space $P \cap P'_M$ is finite-dimensional and $$\dim_k (P \cap P'_M) + \#\iota \;\le\; \sum_i \dim_k \mathcal L(M \cdot \bar D_i) + \dim_k (P \cap P'),$$ where the last term is the `Module.finrank` of $P \cap P'$, hence $0$ should that space fail to be finite-dimensional, and $\mathcal L(\cdot)$ denotes the Riemann–Roch space of a divisor on $\bar F_i/k$. No restriction on the characteristic of $L$ is imposed.
--
--   This is the dimension estimate, of the type used by Deuring in comparing a function field with its reductions, that governs twisted sections of a complete family of regular prolongations of a valuation ring; the spaces $P$ and $P'_M$ play the role of sections regular on the two affine pieces determined by $f$ and $f^{-1}$. It is the analytic core of the genus inequality [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_isAlgClosed), which bounds the sum of the genera of the reductions by the genus of $F/L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le_of_isAlgClosed
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
    (Db : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fb i))
    (hDb : ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
      Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
                u * (f ^ M)⁻¹ ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) ∧
      Module.finrank (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
                u * (f ^ M)⁻¹ ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) + Fintype.card ι ≤
      (∑ i, ell (M • Db i)) +
      Module.finrank (IsLocalRing.ResidueField A)
        ↥(Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
          Submodule.span (IsLocalRing.ResidueField A)
            {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
              (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
              ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) := by sorry
