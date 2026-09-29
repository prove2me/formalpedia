-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
-- name    : CerednikDrinfeld.Omega.exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/13ce8ccb-877a-5828-8c0b-e38039376c7a
-- title:
--   Every point of Ω lies in a translate of the standard affinoid or edge tube
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser for the pair, that is an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that for every nonzero $a \in K_0$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Assume that the associated affinoids exhaust the upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$: every $z \in \Omega$ lies in $\{w : v(w) \le v(\varpi)^{-n} \text{ and } v(w - a) \ge v(\varpi)^{n} \text{ for all } a \in K_0 \text{ with } v(a) \le v(\varpi)^{-n}\}$ for some $n \in \mathbb{N}$. Assume further that the values of $K_0$ lie in the integral powers of $v(\varpi)$: for every nonzero $a \in K_0$ there is $k \in \mathbb{Z}$ with $v(a) = v(\varpi)^k$. Then for every $z \in \Omega$ there exists $g \in \mathrm{PGL}_2(K_0)$ such that, with $w$ the image of $z$ under the Möbius action of $g^{-1}$ on $\mathbb{P}^1(K)$ read back in $K$ (the point at infinity being sent to $0$), either $v(w) \le 1$ and $v(w - a) \ge 1$ for all $a \in K_0$ with $v(a) \le 1$, or else $v(\varpi) < v(w) < 1$.
--
--   This is the elementary input to the reduction of Drinfeld's $p$-adic upper half plane onto the Bruhat–Tits tree: every point of $\Omega$ lies in a $\mathrm{PGL}_2(K_0)$-translate of the affinoid over the standard vertex, or in a translate of the open tube over the standard edge. It is used in the proof that the adic points of the formal model surject onto $\Omega$ ([`CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn`](thm.html#CerednikDrinfeld.FormalOmega.AdicPoint.toOmega_surjOn)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_pmoebius_inv_mem_affinoid_zero_or_v_lt_lt_one_of_isExhausted
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)

    (hval : ∀ a : K₀, a ≠ 0 → ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ k)
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ g : PGL(2, K₀),
      pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0 ∨
      (Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (pmoebius K₀ g⁻¹ z) ∧ Valued.v (pmoebius K₀ g⁻¹ z) < 1) := by sorry
