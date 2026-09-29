-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/dc0014cf-cb77-5171-a38f-28bb446f2975
-- title:
--   Matching residues at a coarsened prolongation are constant
-- statement:
--   Let $L$ be an algebraically closed field and $A \le A_1$ two valuation subrings of $L$, let $F$ be a field extension of $L$, and let $\iota$ be a finite index type. For each $i$ let $\bar F_i$ be a field that is an algebra over the residue field $k = \mathrm{ResidueField}\,A$, and let $R_i$ be a regular prolongation of $A$ to $F$ with residue field $\bar F_i$: that is, a valuation subring $(R_i).\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $(R_i).\mathrm{residue}$ onto $\bar F_i$ whose kernel is the maximal ideal, such that an element of $L$ lies in $(R_i).\mathrm{integers}$ exactly when it lies in $A$, the residue map is compatible with $A \to k \to \bar F_i$, and every nonzero $g \in F$ has a scalar multiple $c\cdot g$ ($c \in L$) in $(R_i).\mathrm{integers}$ with nonzero residue. Assume the valuation subrings $(R_i).\mathrm{integers}$ are pairwise distinct, i.e. $i \mapsto (R_i).\mathrm{integers}$ is injective. Let $f \in F$ lie in every $(R_i).\mathrm{integers}$, be transcendental over $L$, with $F$ finite-dimensional over the intermediate field $L(f)$, let each residue $\bar f_i = (R_i).\mathrm{residue}(f)$ be transcendental over $k$, and assume the completeness relation $\sum_i [\bar F_i : k(\bar f_i)] = [F : L(f)]$. Let further $\bar F_{1,i}$ be fields over $\mathrm{ResidueField}\,A_1$ and $R_{1,i}$ regular prolongations of $A_1$ to $F$ with residue fields $\bar F_{1,i}$, such that $(R_i).\mathrm{integers} \le (R_{1,i}).\mathrm{integers}$ and the residue of $f$ in $\bar F_{1,i}$ is transcendental over $\mathrm{ResidueField}\,A_1$, for every $i$. Let $x, x' \in F$, let $u, u' \in L$ have $A_1$-valuation $1$, and let $t, t' \in L[X]$ each have constant coefficient of $A$-valuation $1$ and all other coefficients of $A$-valuation $< 1$. Assume that $u \cdot x \cdot t(f)$ lies in every $(R_i).\mathrm{integers}$ and in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$, and that $u' \cdot x' \cdot t'(f^{-1})$ lies in every $(R_i).\mathrm{integers}$ and in every valuation subring $V$ of $F$ containing the image of $L$ and $f^{-1}$. Assume finally that $x$ and $x'$ lie in every $(R_{1,i}).\mathrm{integers}$ and have the same image under $(R_{1,i}).\mathrm{residue}$ for every $i$. Then, for a given index $i$, the residue $(R_{1,i}).\mathrm{residue}(x)$ lies in the image of $\mathrm{ResidueField}\,A_1$ in $\bar F_{1,i}$, i.e. equals $\mathrm{algebraMap}\,\kappa$ for some $\kappa \in \mathrm{ResidueField}\,A_1$.
--
--   This is the per-component constancy statement for constant reductions of a function field, in the form needed after coarsening the valuation ring $A$ to $A_1$: a function regular on the chart $f \neq \infty$ of the normalised $f$-model and agreeing, on the fibre, with one regular on the chart $f \neq 0$ has residue constant, that is, scalar, on each component. It is used in the proof of [`AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one), a step in the induction on the rank of the valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A A₁ : ValuationSubring L) (h₁ : A ≤ A₁)
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
    (Fb₁ : ι → Type*) [∀ i, Field (Fb₁ i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A₁) (Fb₁ i)]
    (R₁ : ∀ i, RegularProlongation A₁ F (Fb₁ i))
    (hle : ∀ i, (R i).integers ≤ (R₁ i).integers)
    (htr₁ : ∀ i, Transcendental (IsLocalRing.ResidueField A₁) ((R₁ i).residue ⟨f, hle i (hf i)⟩))
    (x x' : F) (u u' : L) (t t' : L[X])
    (hu : A₁.valuation u = 1) (hu' : A₁.valuation u' = 1)
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (hx : (∀ i, u • x * aeval f t ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u • x * aeval f t ∈ V)
    (hx' : (∀ i, u' • x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u' • x' * aeval f⁻¹ t' ∈ V)
    (hxO : ∀ i, x ∈ (R₁ i).integers) (hx'O : ∀ i, x' ∈ (R₁ i).integers)
    (hxx' : ∀ i, (R₁ i).residue ⟨x, hxO i⟩ = (R₁ i).residue ⟨x', hx'O i⟩) (i : ι) :
    ∃ κ : IsLocalRing.ResidueField A₁,
      (R₁ i).residue ⟨x, hxO i⟩ = algebraMap (IsLocalRing.ResidueField A₁) (Fb₁ i) κ := by sorry
