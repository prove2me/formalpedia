-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_blaschke_denominators
-- name    : CerednikDrinfeld.Omega.exists_blaschke_denominators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/6187cd99-b6b3-55bf-a704-9be58f4deba5
-- title:
--   Blaschke-type denominators for points escaping every affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser of $K_0$ in $K$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$; write $\Omega_n$ for the affinoid consisting of those $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$, and let $\Omega = K \setminus \mathrm{image}(K_0 \to K)$. Assume the affinoids exhaust $\Omega$: every $z \in \Omega$ lies in some $\Omega_n$. Let $(w_\gamma)_{\gamma \in \iota}$ be a family of elements of $K$ with every $w_\gamma \in \Omega$, and suppose that for each $n$ only finitely many $\gamma$ have $w_\gamma \in \Omega_n$. Then there are polynomials $d_\gamma \in K[X]$ with $\deg d_\gamma \le 1$, none of them vanishing at any point of $\Omega$, such that: for every $n$, every $\gamma$ and every $w' \in K$ there is $b \in K$ with $v\big((z - w')/d_\gamma(z)\big) \le v(b)$ for all $z \in \Omega_n$; and for every $n$ and every nonzero $c \in K$, for all but finitely many $\gamma$ one has $v\big((z - w_\gamma)/d_\gamma(z) - 1\big) < v(c)$ for all $z \in \Omega_n$.
--
--   This is the standard construction of compensating linear denominators (Blaschke factors) attached to a family of points of Drinfeld's upper half plane that leaves every affinoid in the exhaustion: after dividing by $d_\gamma$, the factors $z - w_\gamma$ become uniformly bounded on each affinoid and tend uniformly to $1$ there. It supplies the convergence input for the theta-function statements [`CerednikDrinfeld.Omega.exists_holRing_div_eq_theta`](thm.html#CerednikDrinfeld.Omega.exists_holRing_div_eq_theta), [`CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card`](thm.html#CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card) and [`CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul`](thm.html#CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_blaschke_denominators.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_blaschke_denominators
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {ι : Type} (w : ι → K) (hw : ∀ γ, w γ ∈ upperHalfPlane K₀ K)
    (hfin : ∀ n : ℕ, {γ : ι | w γ ∈ affinoid ϖ n}.Finite) :
    ∃ d : ι → Polynomial K,
      (∀ γ, (d γ).natDegree ≤ 1) ∧
      (∀ γ, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0) ∧
      (∀ (n : ℕ) (γ : ι) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b) ∧
      (∀ (n : ℕ) (c : K), c ≠ 0 →
        ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v ((z - w γ) / (d γ).eval z - 1) < Valued.v c) := by sorry
