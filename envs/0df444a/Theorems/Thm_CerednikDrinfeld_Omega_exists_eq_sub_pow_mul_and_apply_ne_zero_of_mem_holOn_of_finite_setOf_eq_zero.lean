-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
-- name    : CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b95a20c9-e7fb-540e-9ef3-ce0444b744eb
-- title:
--   Finite order of vanishing at a point of a closed disc
-- statement:
--   Let $K$ be a field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, complete for the induced topology and algebraically closed, and assume the rank-one condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $S \subseteq K$ and let $f \colon S \to K$ lie in the subring $\mathrm{holOn}\,K\,S$, that is, there is a sequence of rational pairs $r_k$ over $K$, each pole-free on $S$, whose values $v((r_k)(z))$ are bounded by $v(b)$ for a single $b \in K$ uniformly in $k$ and $z \in S$, and such that $z \mapsto (r_k)(z)$ converges uniformly on $S$ to $f$. Assume the zero set $\{z \in S : f(z) = 0\}$ is finite. Let $p \in S$ and let $r \in K$ be non-zero with the closed disc $\{w \in K : v(w - p) \le v(r)\}$ contained in $S$. Then there are $k \in \mathbb{N}$ and $g \colon S \to K$ in $\mathrm{holOn}\,K\,S$ with $g(p) \neq 0$ and $f(z) = (z - p)^k\, g(z)$ for all $z \in S$.
--
--   This is the statement that a rigid-holomorphic function with finitely many zeros vanishes to finite order at any point around which a closed disc of non-zero radius lies in the domain, the factor being extracted inside the same ring of holomorphic functions. It feeds the global factorisation of such a function as a finite product of powers of linear factors times a nowhere-vanishing holomorphic function, [`CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero`](thm.html#CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_of_finite_setOf_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_of_finite_setOf_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (hfin : Set.Finite {z : ↥S | f z = 0})
    (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v r → w ∈ S) :
    ∃ (k : ℕ) (g : ↥S → K), g ∈ holOn K S ∧ g p ≠ 0 ∧
      ∀ z : ↥S, f z = ((z : K) - (p : K)) ^ k * g z := by sorry
