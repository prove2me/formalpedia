-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
-- name    : CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/d4f1051f-876c-5205-8cc7-808f5fd72de4
-- title:
--   Lower bound for a zero-free holomorphic function on a residue class
-- statement:
--   Let $K$ be a field, complete and algebraically closed, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume the rank-one condition that for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $S \subseteq K$ be a subset, let $a, \pi \in K$ with $\pi \neq 0$, and let $Z$ be a finite subset of $K$ such that $v(a - \zeta) = v(\pi)$ for every $\zeta \in Z$. Assume $S$ contains every $z \in K$ with $v(z - a) \le v(\pi)$ and $v(\pi) \le v(z - \zeta)$ for all $\zeta \in Z$. Let $f : S \to K$ lie in the subring $\mathtt{holOn}\ K\ S$, i.e.\ there are rational pairs $r_k$ over $K$, each pole-free on $S$, whose values $v((r_k)(z))$ are bounded by $v(b)$ for a single $b \in K$ uniformly in $k$ and $z \in S$, and with $z \mapsto (r_k)(z)$ converging uniformly on $S$ to $f$. Assume $f(z) \neq 0$ for every $z \in S$ with $v(z - a) < v(\pi)$. Then there exists $\delta \in K$, $\delta \neq 0$, such that $v(\delta) \le v(f(z))$ for every $z \in S$ with $v(z - a) < v(\pi)$.
--
--   This is the single-residue-class core of the non-archimedean minimum modulus principle: a holomorphic function with no zero on the open residue class $\{v(z-a) < v(\pi)\}$ inside the closed disc $\{v(z-a) \le v(\pi)\}$ punctured at the residue classes of the points of $Z$ is bounded away from $0$ there. It is used to produce uniform lower bounds for holomorphic functions on affinoids and on tubes in the Čerednik–Drinfeld rigid-analytic setting, being cited by [`CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero`](thm.html#CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero) and [`CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero`](thm.html#CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (a π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v (a - ζ) = Valued.v π)
    (hS : ∀ z : K, Valued.v (z - a) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S)
    (h0 : ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → Valued.v δ ≤ Valued.v (f z) := by sorry
