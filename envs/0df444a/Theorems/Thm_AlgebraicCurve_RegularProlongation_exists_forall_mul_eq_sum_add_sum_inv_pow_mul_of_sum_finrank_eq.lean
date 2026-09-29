-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/30a1c8e7-d98e-5e34-992a-e0a22de8fda2
-- title:
--   Finite generation of the overlap module over a valuation ring
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\iota$ a finite index type with fields $Fb_i$ over the residue field $k$ of $A$. For each $i$ let $R_i$ be a regular prolongation of $A$ to $F$ with values in $Fb_i$: a valuation subring $(R_i).\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $\mathrm{residue}$ onto $Fb_i$ whose kernel is the maximal ideal, such that $\mathrm{algebraMap}\,c \in (R_i).\mathrm{integers} \iff c \in A$, the residue map is compatible with $A \to k$, and every nonzero element of $F$ has an $L$-multiple lying in $(R_i).\mathrm{integers}$ with nonzero residue. Assume the valuation subrings $(R_i).\mathrm{integers}$ are pairwise distinct, $f \in F$ lies in all of them, $f$ is transcendental over $L$, $F$ is finite-dimensional over $L(f)$ of degree $n$, each residue $\bar f_i$ is transcendental over $k$, and $\sum_i [Fb_i : k(\bar f_i)] = n$. Then there are $z : \mathrm{Fin}\,n \to F$ and $m_0 \in \mathbb{N}$ such that every $z_\sigma$ lies in each $(R_i).\mathrm{integers}$ and in every valuation subring $V$ of $F$ containing $L$ and $f$, while $f^{-m_0} z_\sigma$ lies in every valuation subring containing $L$ and $f^{-1}$, with the following property. Let $x \in F$ admit $p, t \in L[X]$ with all coefficients of $p$ in $A$, one coefficient $t_d$ of valuation $1$ and all others of valuation $< 1$, and $x\, t(f) = p(f)$; let $s \in F$ lie in each $(R_i).\mathrm{integers}$ and in every valuation subring containing $L$ and $f$. Then there exist $lp, lm : \mathrm{Fin}\,n \to F$ and $a : \mathrm{Fin}\,n \to \mathrm{Fin}\,m_0 \to L$ such that each $lp_\sigma$ is of the form $p(f)/t(f)$ and each $lm_\sigma$ of the form $p(f^{-1})/t(f^{-1})$, with $p$ having coefficients in $A$ and $t$ having constant coefficient of valuation $1$ and all other coefficients of valuation $< 1$, each $a_{\sigma k} \in A$, and $$x s = \sum_\sigma lp_\sigma z_\sigma + \sum_\sigma lm_\sigma \bigl(f^{-m_0} z_\sigma\bigr) + \sum_\sigma \sum_{k < m_0} a_{\sigma k}\, f^{-k} z_\sigma .$$
--
--   This is the explicit form of the finiteness of $H^1$ of the structure sheaf for the two-chart model of $F$ over the valuation ring $A$ determined by a complete family of regular prolongations: the module of sections over the overlap is the sum of the two chart modules together with the finitely many $A$-multiples $f^{-k} z_\sigma$, $k < m_0$, built on a Gauss basis $z$. It is used in the construction of reductions of elements of the function field, namely in [`AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one) and [`AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
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
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F) (m₀ : ℕ),
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f⁻¹ ∈ V →
        (f⁻¹) ^ m₀ * z σ ∈ V) ∧
      ∀ (x s : F),
        (∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
          (∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1) ∧
          x * aeval f t = aeval f p) →
        (∀ i, s ∈ (R i).integers) →
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V) →
        ∃ (lp lm : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F)
          (a : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → Fin m₀ → L),
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lp σ * aeval f t = aeval f p) ∧
          (∀ σ, ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
            (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
            lm σ * aeval f⁻¹ t = aeval f⁻¹ p) ∧
          (∀ σ k, a σ k ∈ A) ∧
          x * s = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) +
            ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) := by sorry
