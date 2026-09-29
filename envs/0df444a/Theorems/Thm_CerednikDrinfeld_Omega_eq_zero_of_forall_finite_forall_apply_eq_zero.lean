-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_forall_finite_forall_apply_eq_zero
-- name    : CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/fb23972d-6e68-5bf5-8cab-d9d6f098e125
-- title:
--   Vanishing off a finite set on every affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, with $K$ complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ (valuations of elements of $K_0$ being taken after the structure map) and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume: (`hrk`) for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; (`hex`) every $z \in K$ outside the image of $K_0$ lies in $\mathrm{affinoid}\ \varpi\ n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z-a)$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$ for some $n$; (`hfin`) for each $n$ there is a finite $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Let $\Psi$ belong to the subring `holRing` of functions on the complement of $K_0$ in $K$ whose restriction to each $\mathrm{affinoid}\ \varpi\ n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles there. If for every $n$ there is a finite subset $Z$ of $\mathrm{affinoid}\ \varpi\ n$ with $\Psi(z) = 0$ for all $z$ in that affinoid outside $Z$, then $\Psi = 0$.
--
--   This is the identity principle for rigid-holomorphic functions on Drinfeld's $p$-adic upper half plane, in the form needed to pass from vanishing off finite sets to identical vanishing. It is used in the construction of the ring homomorphism from the function field of the associated Mumford curve, [`CerednikDrinfeld.exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic`](thm.html#CerednikDrinfeld.exists_ringHom_functionField_invariantFieldOf_eval_of_chartwiseMeromorphic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eq_zero_of_forall_finite_forall_apply_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (Ψ : ↥(holRing ϖ))
    (h : ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧ ∀ z : ↥(affinoid ϖ n), z ∉ Z →
      (Ψ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ = 0) :
    Ψ = 0 := by sorry
