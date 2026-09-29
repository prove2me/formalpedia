-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a1b62362-7346-55b3-bc3d-e2a8b5b74377
-- title:
--   Eventual dimension count for joint residue spans
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, let $A \subseteq L$ be a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, let $F$ be a field extension of $L$, and let $\iota$ be a finite index type. For each $i \in \iota$ let $\bar F_i$ be a field with a $k$-algebra structure and let $R_i$ be a regular prolongation of $A$ to $F$ with residue field $\bar F_i$: a valuation subring $\mathcal O_i \subseteq F$ together with a surjective ring homomorphism $\mathcal O_i \to \bar F_i$ whose kernel is the maximal ideal of $\mathcal O_i$, such that $\mathrm{alg}(x) \in \mathcal O_i$ exactly for $x \in A$, the residue map is compatible with $A \to k$, and every nonzero $f \in F$ has an $L$-multiple lying in $\mathcal O_i$ with nonzero residue. Assume $i \mapsto \mathcal O_i$ is injective, that $f \in F$ lies in every $\mathcal O_i$, that $f$ is transcendental over $L$ with $F$ finite over $L(f)$, that each residue $\bar f_i$ is transcendental over $k$, and that $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Let $\bar D_i$ be the divisor on $\bar F_i/k$ (a finitely supported $\mathbb Z$-valued function on the places of $\bar F_i$ over $k$) given by $\bar D_i(w) = \max(0, -\mathrm{ord}_w \bar f_i)$. Write $\rho(T) \subseteq \prod_i \bar F_i$ for the $k$-span of the joint residue vectors $(\overline{u}_i)_i$ of those $u$ lying in all $\mathcal O_i$ and in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$; write $\rho(T'_M)$ for the $k$-span of the joint residues of those $u$ in all $\mathcal O_i$ with $u (f^M)^{-1} \in V$ for every such $V$ containing $f^{-1}$ instead, and $\rho(T')$ for the analogous span with the condition $u \in V$. Then there exists $M_0 \in \mathbb N$ such that for every $M \ge M_0$ the intersection $\rho(T) \cap \rho(T'_M)$ is finite dimensional over $k$ and $$\dim_k\bigl(\rho(T) \cap \rho(T'_M)\bigr) + \#\iota \le \sum_i \ell(M \cdot \bar D_i) + \dim_k\bigl(\rho(T) \cap \rho(T')\bigr),$$ where $\ell(D)$ denotes the $k$-dimension of the Riemann–Roch space of $D$ and the last rank is interpreted as $0$ should that intersection fail to be finite dimensional.
--
--   This is the numerical heart of the semicontinuity comparison between a one-variable function field $F/L$ and the residue function fields $\bar F_i/k$ of a complete family of regular prolongations of a valuation of $L$: the two residue spans play the roles of the affine and the infinite chart of the $f$-model, and the inequality compares their intersection after twisting by $f^M$ with the Riemann–Roch numbers of the pole divisors $\bar D_i$. It is used to derive the genus inequality $\sum_i g(\bar F_i) \le g(F)$ in [`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
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
