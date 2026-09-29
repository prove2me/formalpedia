-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one
-- name    : AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3601d07c-3a0c-5003-b01d-f7e10fb1cb04
-- title:
--   Rank-one induction step for constancy modulo a coarsening
-- statement:
--   Let $L$ be an algebraically closed field, $A$ a valuation subring of $L$ with residue field $k$, and $F$ a field extension of $L$. Let $\iota$ be a finite index type and, for each $i$, let $Fb_i$ be a field over $k$ and $R_i$ a regular prolongation of $A$ to $F$ with residue field $Fb_i$: a valuation subring $(R_i).\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $\mathrm{res}_i$ onto $Fb_i$ whose kernel is the maximal ideal, such that $a\in L$ lies in $A$ exactly when its image in $F$ lies in $(R_i).\mathrm{integers}$, $\mathrm{res}_i$ restricted to $A$ is the residue map $A\to k$ followed by $k\to Fb_i$, and every nonzero element of $F$ has an $L$-multiple lying in $(R_i).\mathrm{integers}$ with nonzero residue. Assume the prolongations are pairwise distinct (the assignment $i\mapsto (R_i).\mathrm{integers}$ is injective), that $f\in F$ lies in all $(R_i).\mathrm{integers}$, is transcendental over $L$ with $F$ finite over $L(f)$, that each residue $\bar f_i=\mathrm{res}_i(f)$ is transcendental over $k$, and that $\sum_i [Fb_i:k(\bar f_i)]=[F:L(f)]$. Let $A\le A_1\le A_2$ be valuation subrings of $L$, and assume the valuation subring $A_1.\mathrm{residueValuationSubring}\,A_2$ of the residue field of $A_2$, namely the image of $A_1$ under the residue map of $A_2$, has Krull dimension at most $1$. Call $u\in F$ $f$-regular if $u$ lies in every $(R_i).\mathrm{integers}$ and in every valuation subring of $F$ containing the image of $L$ and $f$, and $f^{-1}$-regular if it lies in every $(R_i).\mathrm{integers}$ and in every valuation subring of $F$ containing the image of $L$ and $f^{-1}$; call $t\in L[X]$ $d$-good if $v_A(t_d)=1$ and $v_A(t_j)<1$ for $j\neq d$. For a valuation subring $B$ of $L$ write $\Theta(B)$ for the assertion: whenever $m\in L$ has $v_B(m)<1$, $t,t'$ are $0$-good, $s$ is $d$-good, $x\,t(f)$ and $y\,s(f)$ are $f$-regular, $x'\,t'(f^{-1})$ is $f^{-1}$-regular and $x-x'=my$, there exist $a\in A$, $m_1,m_2\in L$ with $v_B(m_1)<1$, $v_B(m_2)<1$, $p,p'\in F$ and $0$-good $r,r'\in L[X]$ such that $p\,r(f)$ is $f$-regular, $p'\,r'(f^{-1})$ is $f^{-1}$-regular, $x=a+m_1p$ and $x'=a+m_2p'$. The theorem asserts that $\Theta(A_2)$ implies $\Theta(A_1)$, the latter being stated for arbitrary given data $m,x,x',y,t,t',s,d$ satisfying the above hypotheses relative to $A_1$.
--
--   This is the inductive step, along a coarsening of valuations of $L$ whose relative residue valuation ring has rank at most one, in the proof that the constants of the two-chart complex of the normalised $f$-model, reduced modulo the maximal ideal of a coarsening, come from $A$ — the form of Zariski's connectedness theorem used for the constant reduction of a function field. It is cited by [`AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top`](thm.html#AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_ringKrullDim_lt_top), where the step is iterated along a chain of coarsenings of finite rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ValuationSubring_ResidueValuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one
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
    (A₁ A₂ : ValuationSubring L) (h₁ : A ≤ A₁) (h₁₂ : A₁ ≤ A₂)
    [Ring.KrullDimLE 1 (A₁.residueValuationSubring A₂ h₁₂)]
    (hΘ : ∀ (m : L) (x x' y : F) (t t' s : L[X]) (d : ℕ),
      A₂.valuation m < 1 →
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) →
      (A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1) →
      (A.valuation (s.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (s.coeff j) < 1) →
      ((∀ i, x * aeval f t ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → x * aeval f t ∈ V) →
      ((∀ i, x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          x' * aeval f⁻¹ t' ∈ V) →
      ((∀ i, y * aeval f s ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → y * aeval f s ∈ V) →
      x - x' = algebraMap L F m * y →
      ∃ (a : A) (m₁ m₂ : L) (p p' : F) (r r' : L[X]),
        A₂.valuation m₁ < 1 ∧ A₂.valuation m₂ < 1 ∧
        (A.valuation (r.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r.coeff j) < 1) ∧
        (A.valuation (r'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r'.coeff j) < 1) ∧
        ((∀ i, p * aeval f r ∈ (R i).integers) ∧
          ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → p * aeval f r ∈ V) ∧
        ((∀ i, p' * aeval f⁻¹ r' ∈ (R i).integers) ∧
          ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
            p' * aeval f⁻¹ r' ∈ V) ∧
        x = algebraMap L F a + algebraMap L F m₁ * p ∧
        x' = algebraMap L F a + algebraMap L F m₂ * p')
    (m : L) (x x' y : F) (t t' s : L[X]) (d : ℕ)
    (hm : A₁.valuation m < 1)
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (hs : A.valuation (s.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (s.coeff j) < 1)
    (hx : (∀ i, x * aeval f t ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : (∀ i, x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        x' * aeval f⁻¹ t' ∈ V)
    (hy : (∀ i, y * aeval f s ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → y * aeval f s ∈ V)
    (hxy : x - x' = algebraMap L F m * y) :
    ∃ (a : A) (m₁ m₂ : L) (p p' : F) (r r' : L[X]),
      A₁.valuation m₁ < 1 ∧ A₁.valuation m₂ < 1 ∧
      (A.valuation (r.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r.coeff j) < 1) ∧
      (A.valuation (r'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r'.coeff j) < 1) ∧
      ((∀ i, p * aeval f r ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → p * aeval f r ∈ V) ∧
      ((∀ i, p' * aeval f⁻¹ r' ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          p' * aeval f⁻¹ r' ∈ V) ∧
      x = algebraMap L F a + algebraMap L F m₁ * p ∧
      x' = algebraMap L F a + algebraMap L F m₂ * p' := by sorry
