-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
-- name    : CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/95534262-0cf9-58e1-a983-128243a23a9a
-- title:
--   Mittag-Leffler splitting of a rational function at a disc
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and suppose $K$ is algebraically closed. Let $Q$ be a `RatPair` over $K$, that is a pair of polynomials $Q.\mathrm{num}, Q.\mathrm{den} \in K[X]$, and let $t_0, \pi_0 \in K$ with $\pi_0 \neq 0$. The assertion is that there exist `RatPair`s $A$ and $B$ over $K$ with the following four properties. First, $A.\mathrm{den}$ has no zero on the set $\{z : Q.\mathrm{den}(z) \neq 0\} \cup \{z : v(\pi_0) \le v(z - t_0)\}$, the union of the non-vanishing locus of $Q.\mathrm{den}$ with the complement of the open disc of radius $v(\pi_0)$ about $t_0$. Second, $\deg A.\mathrm{num} < \deg A.\mathrm{den}$ as elements of $\mathbb{N} \cup \{-\infty\}$. Third, $B.\mathrm{den}$ has no zero on $\{z : Q.\mathrm{den}(z) \neq 0\} \cup \{z : v(z - t_0) < v(\pi_0)\}$. Fourth, for every $z \in K$ with $Q.\mathrm{den}(z) \neq 0$ one has the identity of quotients in $K$
--   $$\frac{Q.\mathrm{num}(z)}{Q.\mathrm{den}(z)} = \frac{A.\mathrm{num}(z)}{A.\mathrm{den}(z)} + \frac{B.\mathrm{num}(z)}{B.\mathrm{den}(z)}.$$
--
--   This is the rational Mittag-Leffler decomposition on $\mathbf{P}^1$: a rational function is written as the sum of the part of its polar divisor lying in an open disc (a proper rational function, vanishing at infinity) and the part lying outside it. It is used in the rigid-analytic part of the Čerednik–Drinfeld material, where it feeds the statement that a function holomorphic on each of two pieces of $\Omega$ is holomorphic on their union.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (Q : RatPair K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) :
    ∃ A B : RatPair K,
      A.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v π₀ ≤ Valued.v (z - t₀)}) ∧
      A.num.degree < A.den.degree ∧
      B.IsPoleFreeOn ({z | Q.den.eval z ≠ 0} ∪ {z | Valued.v (z - t₀) < Valued.v π₀}) ∧
      ∀ z : K, Q.den.eval z ≠ 0 → Q.evalAt z = A.evalAt z + B.evalAt z := by sorry
