-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
-- name    : CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/df40da5a-bba6-5c6d-8243-f21bbe4d941b
-- title:
--   Factorisation at a point: F=(w-z)^{ord_z F}G with G(z)≠ 0
-- statement:
--   Let $K_0$ be a field and $K$ a field extension of it (as a $K_0$-algebra) carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Assume the rank-one condition that for all $x,y\in K$ with $v(x)<1$ and $y\neq 0$ there is $n\in\mathbb N$ with $v(x)^n\le v(y)$, and that $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi\in K_0$ with $0<v(\varpi)<1$ such that every non-zero $a\in K_0$ satisfies $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$ for some $N$, and write $\mathfrak p=v(\varpi)$. Assume the affinoids of $\varpi$ exhaust the Drinfeld upper half plane $\Omega=K\setminus K_0$, i.e. every $z\in\Omega$ lies in some $\{z: v(z)\le \mathfrak p^{-n},\ \mathfrak p^{n}\le v(z-a)\text{ for all }a\in K_0\text{ with }v(a)\le\mathfrak p^{-n}\}$, and assume the finiteness hypothesis that for each $n$ there is a finite set $T\subseteq K_0$ such that every $a\in K_0$ with $v(a)\le\mathfrak p^{-n}$ satisfies $v(a-t)<\mathfrak p^{n}$ for some $t\in T$. Let $F$ be a non-zero element of the ring of functions $\Omega\to K$ which on each affinoid are uniform limits of uniformly bounded pole-free rational functions, and let $z\in\Omega$. Then there is $G$ in that same ring with $F=(w-z)^{m}\,G$, where $w-z$ denotes the coordinate function minus the constant $z$ and $m=\mathrm{ord}_z F$ is the supremum of the set of $n$ with $(w-z)^n\mid F$, and with $G(z)\neq 0$.
--
--   This is the local factorisation (Weierstrass-type) statement for rigid-holomorphic functions on Drinfeld's upper half plane: the vanishing order at a point of $\Omega$ is attained by an honest factorisation with non-vanishing cofactor. It is the form used downstream to recognise the local ring at a point of $\Omega$ as a discrete valuation ring and, more generally, in the divisibility and descent arguments for holomorphic functions and automorphic forms on $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)

    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) :
    ∃ G : ↥(Omega.holRing ϖ),
      F = Omega.coordSub ϖ z ^ Omega.ordAt ϖ F z * G ∧ (G : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by sorry
