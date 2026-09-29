-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
-- name    : AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/83b943f2-de70-54a8-a7e2-a9a3ea6510e4
-- title:
--   Divisibility of Pic⁰ by integers invertible in K
-- statement:
--   Let $K$ be an algebraically closed field of exponential characteristic $p$ (so `ExpChar K p` holds), and assume that every element $a$ of $K$ satisfies $a^{p^n} = a$ for some $n > 0$, i.e. lies in a finite subfield. Let $L'$ be a field equipped with a $K$-algebra structure and a $\mathrm{RatFunc}\,K$-algebra structure compatible with it via `IsScalarTower K (RatFunc K) L'`, and suppose $L'$ is finite-dimensional over the rational function field $\mathrm{RatFunc}\,K = K(X)$. The conclusion is that for every integer $m$ whose image in $K$ is nonzero, and every class $x$ in $\mathrm{Pic}^0(K, L')$, there is a class $y$ with $m \bullet y = x$; that is, the group $\mathrm{Pic}^0(K, L')$ is $m$-divisible. Here $\mathrm{Pic}^0(K,L')$ is the project's degree-zero divisor class group of $L'/K$: divisors are finitely supported functions from the places of $L'$ over $K$ to $\mathbb{Z}$, `Divisor.degZero` is the kernel of the degree map, `Divisor.principal` is the subgroup of divisors of the form $v \mapsto \mathrm{ord}_v(f)$ for some $f \neq 0$ in $L'$, and $\mathrm{Pic}^0$ is the quotient of the former by the latter.
--
--   This is the divisibility of the degree-zero divisor class group (the group of $K$-points of the Jacobian) by any integer invertible in $K$, for a function field in one variable over an algebraically closed field of this special kind. It supplies the divisibility input used in the finiteness statement [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self
    (K : Type u) [Field K] [IsAlgClosed K]
    (p : ℕ) [ExpChar K p] (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'] :
    ∀ m : ℤ, (m : K) ≠ 0 → ∀ x : Pic0 K L', ∃ y : Pic0 K L', m • y = x := by sorry
