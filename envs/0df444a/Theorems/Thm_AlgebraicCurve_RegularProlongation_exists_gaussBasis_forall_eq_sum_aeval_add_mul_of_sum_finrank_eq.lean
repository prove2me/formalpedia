-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b2721caa-35c4-55dd-8c11-cf56fe35a1f7
-- title:
--   Gauss basis with residual generation for complete regular prolongations
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $k = \mathrm{ResidueField}(A)$, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $F_i$ be a field extension of $k$ together with a `RegularProlongation` $R_i$ of $A$ to $F$ with residue field $F_i$: that is, a valuation subring $\mathcal O_i = (R_i).\mathrm{integers}$ of $F$, a ring homomorphism $\mathrm{res}_i : \mathcal O_i \to F_i$ such that for $x \in L$ one has $x \in \mathcal O_i$ iff $x \in A$, $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal O_i$, $\mathrm{res}_i$ agrees on $A$ with $A \to k \to F_i$, and every nonzero $g \in F$ admits $c \in L$ with $c g \in \mathcal O_i$ and $\mathrm{res}_i(cg) \neq 0$. Assume $i \mapsto \mathcal O_i$ is injective; let $f \in F$ satisfy $f \in \mathcal O_i$ for all $i$, be transcendental over $L$, have $F$ finite-dimensional over the intermediate field $L(f)$, have each residue $\bar f_i = \mathrm{res}_i(f)$ transcendental over $k$, and satisfy the completeness relation $\sum_i [F_i : k(\bar f_i)] = n$, where $n = [F : L(f)]$. Call $w \in F$ Gauss-integral if $w \cdot q(f) = p(f)$ for some $p, q \in L[X]$ with all coefficients of $p$ in $A$ and $q$ primitive (all coefficients of valuation $\le 1$, some coefficient of valuation exactly $1$), and Gauss-infinitesimal if the same holds with all coefficients of $p$ of valuation $< 1$. The conclusion asserts the existence of $z : \mathrm{Fin}\, n \to F$ such that: each $z_\sigma$ lies in every $\mathcal O_i$; each $z_\sigma$ lies in every valuation subring $V$ of $F$ containing the image of $L$ and containing $f$; the family $z$ is linearly independent over $L(f)$; every $b \in F$ lying in all the $\mathcal O_i$ can be written $b = \sum_\sigma w_\sigma z_\sigma$ with all $w_\sigma$ Gauss-integral; and, for every $y \in F$ lying in all valuation subrings of $F$ containing the image of $L$ and $f$, and every Gauss-integral family $w$ with $y = \sum_\sigma w_\sigma z_\sigma$, there are polynomials $C_{1,\sigma} \in L[X]$ with all coefficients in $A$ and Gauss-infinitesimal elements $\mu_\sigma \in F$ with $y = \sum_\sigma (C_{1,\sigma}(f) + \mu_\sigma) z_\sigma$.
--
--   This is the constant-reduction statement that a complete family of regular prolongations of a valuation $A$ to a function field $F = L(f, \dots)$ admits a Gauss basis: an $L(f)$-basis of elements integral at all the $\mathcal O_i$ and at all valuation rings of $F$ containing $L[f]$, with respect to which both the intersection $\bigcap_i \mathcal O_i$ and, modulo the maximal ideal of the Gauss ring, the integral closure of $L[f]$ are generated over the Gauss valuation ring of $L(f)$. It feeds the construction of integral bases on the chart $f \neq \infty$ of a model of $F$ over $A$ and is cited by [`AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
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
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
          (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            w σ * aeval f q = aeval f p) ∧
          b = ∑ σ, w σ * z σ) ∧
      (∀ (y : F) (w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
        (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          w σ * aeval f q = aeval f p) →
        y = ∑ σ, w σ * z σ →
        ∃ (C₁ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → L[X])
          (μ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
          (∀ σ j, (C₁ σ).coeff j ∈ A) ∧
          (∀ σ, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            μ σ * aeval f q = aeval f p) ∧
          y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ) := by sorry
