-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
-- name    : CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/9510347c-7661-5c36-8742-586c2b352146
-- title:
--   Divisibility by w-z at a zero of a holomorphic function on Ω
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser, that is, an element $\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ and such that for every $a \in K_0^\times$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Assume further: (i) for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$; (ii) $\varpi$ is exhausting, i.e. every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ lies in one of the affinoids $\{z : v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z-a)$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$. Let $F$ belong to the ring of functions $\Omega \to K$ whose restriction to each such affinoid is a uniform limit of evaluations of rational functions pole-free on that affinoid with valuations bounded uniformly, and let $z \in \Omega$ with $F(z) = 0$. Then $F$ is divisible, inside that ring, by the element $\mathrm{coordSub}\ \varpi\ z$, namely the coordinate function $w \mapsto w$ minus the constant $z$.
--
--   This is the removable-zero (Weierstrass division) step for rigid-holomorphic functions on Drinfeld's upper half plane: a zero of $F$ at $z$ can be divided out by the local parameter $w - z$. It underlies the order-of-vanishing calculus on $\Omega$, being used to compare vanishing orders with divisibility and to factor a function as a power of $w-z$ times a function not vanishing at $z$, and hence in the construction of valuations on invariant subfields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K))
    (hF : (F : ↥(upperHalfPlane K₀ K) → K) z = 0) :
    coordSub ϖ z ∣ F := by sorry
