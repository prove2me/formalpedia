-- Prove2me | Theorems.Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
-- name    : Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/76b6771f-fd7e-5b8a-8d69-41396668f511
-- title:
--   Clearing denominators: a nonzero q₀∈ L[f] with q₀z valuation-integral
-- statement:
--   Let $L$ and $F$ be fields with $F$ an $L$-algebra, and let $f\in F$ be such that $F$ is finite-dimensional over the intermediate field $L(f)=\mathrm{IntermediateField.adjoin}\,L\,\{f\}$. Then for every $z\in F$ there is an element $q_0$ of the $L$-subalgebra $L[f]=\mathrm{Algebra.adjoin}\,L\,\{f\}$ of $F$ with $q_0\neq 0$ such that, for every valuation subring $V$ of $F$ with the property that $V$ contains the image of $L$ under the structure map $L\to F$ (that is, $\mathrm{algebraMap}\,L\,F\,a\in V$ for all $a\in L$) and $f\in V$, the product $q_0\,z$ (with $q_0$ viewed in $F$) lies in $V$. The conclusion is thus a single choice of $q_0$, depending on $z$ but uniform in $V$: by Krull's characterisation of the integral closure as the intersection of the valuation subrings containing a given subring, this says precisely that $q_0z$ is integral over $L[f]$.
--
--   This is the standard denominator-clearing step for an element of $F$ relative to the subalgebra $L[f]$: over the fraction field $L(f)$ the element $z$ is integral, and a single nonzero element of $L[f]$ suffices to push it into the integral closure, stated here in the valuation-theoretic form that is convenient downstream. It is used in the construction of regular prolongations and Gauss bases on algebraic curves, and in the lemma producing a polynomial whose residue is nonzero and whose value multiplied by a given element lies in a valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by sorry
