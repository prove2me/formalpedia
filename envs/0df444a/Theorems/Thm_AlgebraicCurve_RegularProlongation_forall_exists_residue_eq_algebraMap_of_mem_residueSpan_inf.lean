-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
-- name    : AlgebraicCurve.RegularProlongation.forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/39ad9d52-5a69-5d97-ad21-27fc72f17263
-- title:
--   Joint residues in ρ(T)∩ρ(T') have constant components
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, let $A \subseteq L$ be a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, let $F$ be a field extension of $L$, and let $\iota$ be a finite index type. For each $i$ let $F_i$ be a field with a $k$-algebra structure and let $R_i$ be a regular prolongation of $A$ to $F$ with residue field $F_i$: a valuation subring $\mathcal O_i \subseteq F$ together with a surjective ring homomorphism $\mathcal O_i \to F_i$ whose kernel is the maximal ideal of $\mathcal O_i$, such that for $x \in L$ one has $x \in \mathcal O_i$ iff $x \in A$, the induced map on residues extends $k \to F_i$, and every nonzero $g \in F$ has an $L$-multiple lying in $\mathcal O_i$ with nonzero residue. Assume $i \mapsto \mathcal O_i$ is injective; let $f \in F$ lie in every $\mathcal O_i$, be transcendental over $L$, with $F$ finite-dimensional over $L(f)$, with each residue $\bar f_i \in F_i$ transcendental over $k$, and with $\sum_i [F_i : k(\bar f_i)] = [F : L(f)]$. Let $h \in \prod_i F_i$ lie in both of the following $k$-submodules: the $k$-span of the tuples of residues $(\overline{u}_i)_i$ of elements $u \in \bigcap_i \mathcal O_i$ that belong to every valuation subring $V$ of $F$ containing the image of $L$ and containing $f$, and the $k$-span of the same set of tuples with $f$ replaced by $f^{-1}$. Then for every $i$ the component $h_i$ lies in the image of $k \to F_i$.
--
--   This is the componentwise half of the constancy statement for joint residues: for each place of the special fibre, an element of the intersection of the two spans (the residues of the integral closures of $L[f]$ and of $L[f^{-1}]$ in $F$) has residue a constant of $k$, the analogue of the fact that global sections of a proper curve over an algebraically closed field are constants. It is used by [`AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one), where the remaining point is that the constants attached to the various components agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
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
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∀ i, ∃ c : IsLocalRing.ResidueField A, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by sorry
