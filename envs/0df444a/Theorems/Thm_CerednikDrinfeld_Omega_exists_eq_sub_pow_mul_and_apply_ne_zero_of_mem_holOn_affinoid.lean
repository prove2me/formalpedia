-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
-- name    : CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/1821364a-e173-512c-95ed-f9ce5d96eaef
-- title:
--   Finite vanishing order at a point of a Drinfeld affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$ (valuations of elements of $K_0$ taken after the structure map to $K$). Assume the rank-one condition $(\mathrm{hrk})$: for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$. Fix $n \in \mathbb{N}$ and assume the finiteness condition $(\mathrm{hfin})$: there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Write $\Omega_n =$ `affinoid ϖ n` for the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z - a)$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $f : \Omega_n \to K$ lie in the subring `holOn` of functions that are uniform limits on $\Omega_n$ of a sequence of rational functions, each pole-free on $\Omega_n$, whose values on $\Omega_n$ are bounded in absolute value by a single constant $v(b)$; assume $f$ is not identically zero, and let $p \in \Omega_n$. The conclusion is that there exist $k \in \mathbb{N}$ and $g$ in the same ring `holOn` with $g(p) \ne 0$ and $f(z) = (z - p)^k g(z)$ for all $z \in \Omega_n$.
--
--   This is the statement that a nonzero rigid analytic function on one of the standard affinoids $\Omega_n$ exhausting Drinfeld's upper half-plane vanishes to finite order at each point, together with the factorisation $f = (z-p)^k g$ with $g$ analytic and nonvanishing at $p$. It is the local input for the global factorisation of such a function into a finite product of linear factors times a unit, [`CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid`](thm.html#CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : ∃ z : ↥(affinoid ϖ n), f z ≠ 0)
    (p : ↥(affinoid ϖ n)) :
    ∃ (k : ℕ) (g : ↥(affinoid ϖ n) → K), g ∈ holOn K (affinoid ϖ n) ∧ g p ≠ 0 ∧
      ∀ z : ↥(affinoid ϖ n), f z = ((z : K) - (p : K)) ^ k * g z := by sorry
