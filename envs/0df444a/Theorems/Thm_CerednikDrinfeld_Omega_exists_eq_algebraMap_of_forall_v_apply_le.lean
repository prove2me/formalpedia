-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le
-- name    : CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/66c23f91-196b-53f9-8bf2-5a7b6ac1b887
-- title:
--   Liouville theorem for Drinfeld's upper half plane
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Let $\varpi$ be a pseudo-uniformizer of $K_0$ relative to $K$: an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi) < 1$ (valuations taken after $\mathrm{algebraMap}$) such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. Assume: (hrk) for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n$ with $v(x)^n \le v(y)$; (hex) every $z$ in the upper half plane $\Omega = K \setminus \mathrm{algebraMap}(K_0)$ lies in some affinoid $\{z : v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z - a)$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$; (hfin) for each $n$ there is a finite $T \subseteq K_0$ such that each $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ has some $t \in T$ with $v(a - t) < v(\varpi)^n$. Let $f$ lie in the ring of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of rational pairs pole-free there, and suppose $v(f(z)) \le v(b)$ for all $z \in \Omega$ and some $b \in K$. Then $f$ is the constant function attached to some $c \in K$.
--
--   This is Liouville's theorem for Drinfeld's upper half plane: a rigid-holomorphic function on $\Omega = \mathbb{P}^1 \setminus \mathbb{P}^1(K_0)$ that is bounded in absolute value is constant. It is used to identify the constants inside the ring of holomorphic functions on $\Omega$, in particular in the statements [`CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid`](thm.html#CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid) and [`CerednikDrinfeld.Omega.exists_eq_algebraMap_of_isUnit_of_v_apply_eq`](thm.html#CerednikDrinfeld.Omega.exists_eq_algebraMap_of_isUnit_of_v_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_v_apply_le.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_v_apply_le
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (f : ↥(holRing ϖ)) (b : K)
    (hb : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ Valued.v b) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by sorry
