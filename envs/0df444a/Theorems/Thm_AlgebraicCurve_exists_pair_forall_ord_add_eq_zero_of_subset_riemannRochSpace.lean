-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
-- name    : AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/69aef824-6047-531b-8492-1c3abd32274a
-- title:
--   Base-point-free pencils inside a base-point-free linear system
-- statement:
--   Let $K$ be an infinite field and $F$ a field equipped with a $K$-algebra structure, and assume the class `HasPrincipalDivisors K F`: every nonzero $f \in F$ admits a finitely supported function $P$ from the places of $K$-$F$ to $\mathbb{Z}$ with $P(v) = \operatorname{ord}_v f$ at every place $v$ and $\deg P = 0$. Here a place is a valuation subring of $F$ containing $\operatorname{algebraMap}(K)$, distinct from $F$ itself and a principal ideal ring, and $\operatorname{ord}_v f$ is minus the logarithm of its associated adic valuation at $f$. Let $D$ be a divisor, i.e. a finitely supported integer-valued function on places, and let $V$ be a $K$-submodule of $F$, finite-dimensional over $K$, contained in the Riemann–Roch space of $D$ (so every $f \in V$ satisfies $v(f) \le \exp(D(v))$ at every place $v$). Assume $V$ is base-point free: for every place $w$ there is a nonzero $f \in V$ with $\operatorname{ord}_w f + D(w) = 0$. Then there exist $f_1, f_2 \in V$ such that for every place $w$, either $f_1 \neq 0$ and $\operatorname{ord}_w f_1 + D(w) = 0$, or $f_2 \neq 0$ and $\operatorname{ord}_w f_2 + D(w) = 0$.
--
--   This is the classical general-position statement that a base-point-free linear system over an infinite field contains a base-point-free pencil, phrased so that the conclusion also holds when there are no places at all (take $f_1 = f_2 = 0$). It feeds the analysis of linear systems attached to embedding divisors on modular curves, being cited by [`ModularCurve.JZero.riemannRochSpace_embDivisor_mul_eq`](thm.html#ModularCurve.JZero.riemannRochSpace_embDivisor_mul_eq) and [`ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow`](thm.html#ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
    {K F : Type*} [Field K] [Infinite K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (D : AlgebraicCurve.Divisor K F) (V : Submodule K F) [FiniteDimensional K ↥V]
    (hVD : V ≤ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, ∃ f ∈ V, f ≠ 0 ∧ w.ord f + D w = 0) :
    ∃ f₁ ∈ V, ∃ f₂ ∈ V, ∀ w : AlgebraicCurve.Place K F,
      (f₁ ≠ 0 ∧ w.ord f₁ + D w = 0) ∨ (f₂ ≠ 0 ∧ w.ord f₂ + D w = 0) := by sorry
