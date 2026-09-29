-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
-- name    : CerednikDrinfeld.Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e1f24828-9f37-53d1-b743-999c45e85ae2
-- title:
--   Zero-free holomorphic functions on the affinoid Ωₙ are invertible
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure and a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K$ over $K_0$, that is, an element $\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ and such that every non-zero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume further the rank-one condition that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Fix $n \in \mathbb{N}$ and assume there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^{n}$ for some $t \in T$. Let $\Omega_n = \{z \in K : v(z) \le v(\varpi)^{-n} \text{ and } v(z - a) \ge v(\varpi)^{n} \text{ for every } a \in K_0 \text{ with } v(a) \le v(\varpi)^{-n}\}$, and let the holomorphic functions on $\Omega_n$ be the subring of functions $\Omega_n \to K$ that are uniform limits on $\Omega_n$ of sequences of rational functions, each without poles on $\Omega_n$ and all bounded in valuation by one constant $v(b)$. Then for every holomorphic $u$ on $\Omega_n$ with $u(z) \ne 0$ for all $z \in \Omega_n$ there exists a holomorphic $w$ on $\Omega_n$ with $u \cdot w = 1$.
--
--   This is the assertion that a nowhere-vanishing holomorphic function on the affinoid $\Omega_n$ of the Drinfeld upper half plane — a closed disc with finitely many open discs removed — is a unit of the ring of holomorphic functions on it; its analytic content is the minimum modulus principle, the existence of a non-zero lower bound for $v(u)$ on $\Omega_n$. It is used in the divisibility criterion [`CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le`](thm.html#CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le) and in the construction of the ring of invariant holomorphic functions assembled from the affinoids $\Omega_n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {u : ↥(affinoid ϖ n) → K} (hu : u ∈ holOn K (affinoid ϖ n)) (h0 : ∀ z : ↥(affinoid ϖ n), u z ≠ 0) :
    ∃ w : ↥(affinoid ϖ n) → K, w ∈ holOn K (affinoid ϖ n) ∧ u * w = 1 := by sorry
