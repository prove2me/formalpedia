-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
-- name    : CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/77a73cbf-889b-53fa-b3d0-f51205af95a2
-- title:
--   Finite order of vanishing on Drinfeld's upper half plane
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Assume the rank-one condition `hrk`: for all $x,y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$; assume further that $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ (valuation taken after the structure map to $K$) such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Write $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ and, for $n \in \mathbb{N}$, let the $n$-th affinoid be the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Two further hypotheses are imposed: `hex`, that every point of $\Omega$ lies in some affinoid; and `hfin`, that for each $n$ there is a finite subset $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^{n}$ for some $t \in T$. Let $F$ be a nonzero element of the ring $\mathcal{O}(\Omega)$ of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of rational functions without poles there, and let $z \in \Omega$. Then the set of $n \in \mathbb{N}$ such that $(w - z)^n$ divides $F$ in that ring is bounded above.
--
--   This is the finiteness clause underlying the order of vanishing $\operatorname{ord}$ of a rigid-holomorphic function at a point of Drinfeld's upper half plane: since the set of admissible exponents is bounded above, its supremum is attained, and the divisibility and multiplicativity properties of $\operatorname{ord}$ follow. It is cited in the construction of the divisor of a nonzero holomorphic function, in the factorisation of $F$ as a power of the local parameter times a function nonvanishing at $z$, and in the valuation-theoretic analysis of quotients of $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd.lean

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)

    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) :
    BddAbove {n : ℕ | Omega.coordSub ϖ z ^ n ∣ F} := by sorry
