-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le
-- name    : CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/2235abe2-a167-545d-bf04-3b20cfc1e140
-- title:
--   Divisibility in 𝒪(Ω) is decided by orders of vanishing
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra that is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and suppose $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb N$. Assume: (`hrk`) for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n$ with $v(x)^n \le v(y)$, a rank-one condition; (`hex`) the affinoids $\Omega_n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^n$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$ exhaust the Drinfeld upper half plane $\Omega = K \setminus K_0$ (the complement of the image of $K_0$ in $K$); (`hfin`) for each $n$ there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Let $F, G$ lie in the ring $\mathcal O(\Omega)$ of functions $\Omega \to K$ whose restriction to each $\Omega_n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles on $\Omega_n$, with $G \neq 0$, and suppose that for every $z \in \Omega$ the order of vanishing $\operatorname{ord}_z G \le \operatorname{ord}_z F$, where $\operatorname{ord}_z H$ denotes the supremum of those $n$ with $(\mathrm{id} - z)^n \mid H$ in $\mathcal O(\Omega)$. Then $G$ divides $F$ in $\mathcal O(\Omega)$. No hypothesis is imposed on $F$; the case $F = 0$ is included.
--
--   This is the statement that a rigid-meromorphic function $F/G$ on the Drinfeld upper half plane with no poles is holomorphic, i.e. that divisibility in $\mathcal O(\Omega)$ is decided by divisors. It is used in the valuative description of the field of invariant meromorphic functions on $\Omega$ under a discrete group, and in the construction of theta functions attached to principal divisor classes on the resulting curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le.lean

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F G : ↥(holRing ϖ)) (hG : G ≠ 0)
    (h : ∀ z : ↥(upperHalfPlane K₀ K), ordAt ϖ G z ≤ ordAt ϖ F z) :
    G ∣ F := by sorry
