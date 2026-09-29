-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
-- name    : CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/279f20b0-0e9c-52ae-af7c-76e02942c009
-- title:
--   Division by a linear factor for rationally approximable functions
-- statement:
--   Let $K$ be a field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero, and assume $K$ is complete for the valuation topology and algebraically closed. Let $S\subseteq K$ be a subset and let $f\colon S\to K$ lie in the subring $\mathrm{holOn}\,K\,S$, that is: there is a sequence $(r_k)$ of rational pairs over $K$ such that each $r_k$ is pole-free on $S$, the values $v(r_k(z))$ are bounded above by $v(b)$ for a single $b\in K$ uniformly in $k$ and in $z\in S$, and the functions $z\mapsto r_k(z)$ converge uniformly on $S$ to $f$. Suppose $z_0\in S$ satisfies $f(z_0)=0$, and suppose there is $r\in K$ with $r\neq 0$ such that every $z\in K$ with $v(z-z_0)\le v(r)$ belongs to $S$, i.e. $S$ contains the closed disc of radius $v(r)$ about $z_0$. The conclusion is that there exists $g\colon S\to K$ again belonging to $\mathrm{holOn}\,K\,S$ with $f(z)=(z-z_0)\,g(z)$ for every $z\in S$.
--
--   This is Weierstrass division by the linear factor $z-z_0$ in the ring of functions on $S$ that are uniform limits of uniformly bounded pole-free rational functions. Iterating it yields the order of vanishing at an interior point, and it is used in establishing that such a function factors as a power of $z-z_0$ times a nonvanishing function and that the zero set inside a disc is finite, as needed for the local theory of zeros on the affinoids exhausting Drinfeld's upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S) (z₀ : ↥S) (hz₀ : f z₀ = 0)
    (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (z₀ : K)) ≤ Valued.v r → z ∈ S) :
    ∃ g : ↥S → K, g ∈ holOn K S ∧ ∀ z : ↥S, f z = ((z : K) - (z₀ : K)) * g z := by sorry
