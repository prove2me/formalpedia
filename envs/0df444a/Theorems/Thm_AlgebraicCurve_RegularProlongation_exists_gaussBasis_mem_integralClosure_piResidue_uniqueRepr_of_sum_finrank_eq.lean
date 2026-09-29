-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/c81f92bb-448e-591b-b7bd-2720204736a9
-- title:
--   Gauss basis of the common integers, with independent residues
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k =$ `IsLocalRing.ResidueField A`, and $F$ a field extension of $L$. Let $\iota$ be a nonempty finite index type and, for each $i$, let $Fb\,i$ be a field that is a $k$-algebra and $R\,i$ a `RegularProlongation A F (Fb i)`: a valuation subring $(R\,i).\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $(R\,i).\mathrm{residue}$ onto $Fb\,i$ whose kernel is the maximal ideal, such that $\mathrm{algebraMap}\,L\,F\,x$ lies in $(R\,i).\mathrm{integers}$ exactly when $x \in A$, the residue map extends the residue map of $A$ along $k \to Fb\,i$, and every nonzero element of $F$ has an $L$-multiple lying in $(R\,i).\mathrm{integers}$ with nonzero residue. Assume $i \mapsto (R\,i).\mathrm{integers}$ is injective; let $f \in F$ lie in every $(R\,i).\mathrm{integers}$, be transcendental over $L$, with $F$ finite-dimensional over $L(f) =$ `IntermediateField.adjoin L {f}`, and with every residue $\overline{f}_i := (R\,i).\mathrm{residue}\,f$ transcendental over $k$. Fix an index $i_0$ and assume completeness: every valuation subring $W$ of $F$ that agrees with $(R\,i_0).\mathrm{integers}$ on $L(f)$ equals $(R\,j).\mathrm{integers}$ for some $j$. Assume finally the defectlessness equality $\sum_i [Fb\,i : k(\overline{f}_i)] = [F : L(f)]$, where $k(\overline{f}_i) =$ `IntermediateField.adjoin k {`$\overline{f}_i$`}`. Then there are a natural number $d'$ and elements $z_\sigma \in F$, $\sigma \in \mathrm{Fin}\,d'$, each lying in every $(R\,i).\mathrm{integers}$, such that: (1) each $z_\sigma$ lies in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$; (2) for tuples $q, q' : \mathrm{Fin}\,d' \to k[X]$, if $\sum_\sigma q_\sigma(\overline{f}_i)\,\overline{z_\sigma}_{,i} = \sum_\sigma q'_\sigma(\overline{f}_i)\,\overline{z_\sigma}_{,i}$ in $Fb\,i$ for every $i$, then $q = q'$; and (3) every $b \in F$ lying in all the $(R\,i).\mathrm{integers}$ can be written $b = \sum_\sigma c_\sigma z_\sigma$ with $c_\sigma \in L(f)$ all lying in $(R\,i_0).\mathrm{integers}$. No relation between $d'$ and the two equal ranks is asserted.
--
--   This is the Green–Matignon–Pop construction of a basis of the intersection $\bigcap_i (R\,i).\mathrm{integers}$ over the Gauss ring $(R\,i_0).\mathrm{integers} \cap L(f)$, with the basis chosen inside the integral closure of $L[f]$ in $F$ (clause (1)) and with residues satisfying a unique-representation property over $k[X]$ (clause (2)). It feeds the comparison of traces with residues of traces and the corresponding statements for prolongation data on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ : ι)
    (hcomplete : ∀ W : ValuationSubring F,
      (∀ e ∈ IntermediateField.adjoin L ({f} : Set F), e ∈ W ↔ e ∈ (R i₀).integers) →
      ∃ j, W = (R j).integers)
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (d' : ℕ) (z : Fin d' → F) (hzO : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ q q' : Fin d' → Polynomial (IsLocalRing.ResidueField A),
        (∀ i, ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q σ)
            * (R i).residue ⟨z σ, hzO σ i⟩
          = ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' σ)
            * (R i).residue ⟨z σ, hzO σ i⟩) →
        q = q') ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ c : Fin d' → IntermediateField.adjoin L ({f} : Set F),
          (∀ σ, (c σ : F) ∈ (R i₀).integers) ∧ b = ∑ σ, (c σ : F) * z σ) := by sorry
