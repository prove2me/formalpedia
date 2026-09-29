-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/5a30f719-96d8-54a3-8ba8-4f2432b3df6e
-- title:
--   Strassman finiteness of zeros in an open residue class
-- statement:
--   Let $K$ be a field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, complete for the valuation topology and algebraically closed, and assume the rank-one condition $hrk$: for all $x,y\in K$ with $v(x)<1$ and $y\neq0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$. Let $S\subseteq K$ be a set, let $a,\pi\in K$ with $\pi\neq0$, and let $Z$ be a finite subset of $K$ all of whose elements $\zeta$ satisfy $v(a-\zeta)=v(\pi)$. Assume that $S$ contains every $z\in K$ with $v(z-a)\le v(\pi)$ and $v(\pi)\le v(z-\zeta)$ for all $\zeta\in Z$. Let $f\colon S\to K$ lie in the subring $holOn$ of functions on $S$, that is, there is a sequence $r_k$ of pairs of polynomials over $K$, each pole-free on $S$, whose values on $S$ are bounded in valuation by $v(b)$ for a single $b\in K$, and such that $z\mapsto (r_k)(z)$ converges uniformly on $S$ to $f$. Then either $f(z)=0$ for every $z\in S$ with $v(z-a)\le v(\pi)$ and $v(\pi)\le v(z-\zeta)$ for all $\zeta\in Z$, or the set of $z\in S$ with $v(z-a)<v(\pi)$ and $f(z)=0$ is finite.
--
--   This is a Strassman-type finiteness statement for rigid analytic functions, expressed in the rational-approximant formalism used for holomorphic functions on subsets of $K$: on the closed disc of radius $v(\pi)$ about $a$ with the open residue discs about the points of $Z$ removed, a holomorphic function either vanishes identically or has finitely many zeros in the open residue class of $a$. It is the local input to [`CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn`](thm.html#CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn), which globalises the finiteness of zeros over a disc.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (a π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v (a - ζ) = Valued.v π)
    (hS : ∀ z : K, Valued.v (z - a) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) :
    (∀ z : ↥S, Valued.v ((z : K) - a) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) → f z = 0) ∨
      Set.Finite {z : ↥S | Valued.v ((z : K) - a) < Valued.v π ∧ f z = 0} := by sorry
