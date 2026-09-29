-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
-- name    : CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/05d89b7f-2651-5c99-86ca-18821d43148e
-- title:
--   Weierstrass factorisation over a finite zero set
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete for the valuation topology and algebraically closed, and assume the rank-one condition $\mathrm{hrk}$: for all $x,y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $S \subseteq K$ and let $f : S \to K$ lie in the subring $\mathtt{holOn}\ K\ S$, that is, there is a sequence of rational pairs $r_k$ over $K$, each pole-free on $S$, whose evaluations on $S$ are uniformly bounded in valuation by some $v(b)$, and such that $z \mapsto (r_k).\mathtt{evalAt}\ z$ converges uniformly on $S$ to $f$. Assume the zero set $\{z \in S : f(z) = 0\}$ is finite, and that every zero $z$ of $f$ is the centre of a closed disc inside $S$: there is $r \neq 0$ with $\{w \in K : v(w - z) \le v(r)\} \subseteq S$. Then there exist a finite subset $Z$ of $S$, exponents $k : S \to \mathbb{N}$ and $u : S \to K$ such that $u$ again lies in $\mathtt{holOn}\ K\ S$, $u(z) \neq 0$ for every $z \in S$, a point $p \in S$ belongs to $Z$ precisely when $k(p) \ge 1$, and $f(z) = \bigl(\prod_{p \in Z} (z - p)^{k(p)}\bigr) u(z)$ for all $z \in S$.
--
--   This is the Weierstrass-type factorisation of a rigid holomorphic function on a subset of $K$ with finitely many zeros, each an interior point in the strong sense that a closed disc about it lies in the domain: $f$ is a polynomial, given by its zeros with multiplicities, times a nowhere-vanishing holomorphic unit. It feeds the construction of holomorphic functions on the Drinfeld upper half plane through [`CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover`](thm.html#CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})

    (hdisc : ∀ z : ↥S, f z = 0 → ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - (z : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (Z : Finset ↥S) (k : ↥S → ℕ) (u : ↥S → K),
      u ∈ holOn K S ∧ (∀ z : ↥S, u z ≠ 0) ∧
      (∀ p : ↥S, p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥S, f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by sorry
