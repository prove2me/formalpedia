-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero
-- name    : CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/c82b9bcf-44fe-507c-99de-27bd5019eaa9
-- title:
--   Minimum modulus on a tube for zero-free rigid functions
-- statement:
--   Let $K$ be a field equipped with a valuation $v =$ `Valued.v` taking values in a linearly ordered commutative group with zero $\Gamma_0$, complete for the valuation topology and algebraically closed, and assume the rank condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $c_0, R_0 \in K$ with $R_0 \neq 0$, let $H \subset K$ be a finite set, and let $\rho : K \to K$ satisfy $\rho(h) \neq 0$ for every $h \in H$. Let $P \subseteq K$ be a set characterised by the property that $z \in P$ if and only if $v(z - c_0) \le v(R_0)$ and $v(\rho(h)) \le v(z - h)$ for all $h \in H$; that is, $P$ is the closed disc of radius $v(R_0)$ about $c_0$ with the open discs of radius $v(\rho(h))$ about the points $h \in H$ removed. Let $u : P \to K$ lie in the subring `holOn K P`, i.e. there is a sequence of rational functions $r_k$ over $K$, each pole-free on $P$, uniformly bounded on $P$ by $v(b)$ for a single $b \in K$, whose evaluations converge uniformly on $P$ to $u$; and suppose $u(z) \neq 0$ for every $z \in P$. Then there exists $\delta \in K$, $\delta \neq 0$, with $v(\delta) \le v(u(z))$ for all $z \in P$.
--
--   This is the minimum modulus principle for a tube (a closed disc with finitely many open discs deleted): a rigid-holomorphic function without zeros on such a set has valuation bounded below by that of a non-zero constant, so that its inverse is again bounded. It is applied in the construction of functions on the affinoids exhausting Drinfeld's upper half plane, where it feeds the statement [`CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover`](thm.html#CerednikDrinfeld.Omega.exists_polynomial_ne_zero_mul_mem_holOn_of_forall_mem_holOn_mul_eq_linearPiece_cover); the proof reduces to the corresponding bound on a single residue class, [`CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero`](thm.html#CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_tube_of_forall_ne_zero
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))
    {u : ↥P → K} (hu : u ∈ holOn K P) (h0 : ∀ z : ↥P, u z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥P, Valued.v δ ≤ Valued.v (u z) := by sorry
