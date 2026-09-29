-- Prove2me | Theorems.Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
-- name    : Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/c4b1940f-d152-5d64-be44-0420c6f61688
-- title:
--   Uniqueness of Laurent coefficients on an annulus
-- statement:
--   Let $e \colon \mathbb{Z} \to \mathbb{C}$ be a function and let $r_1, r_2$ be real numbers with $0 < r_1$ and $r_1 < r_2$. Assume the two absolute-convergence hypotheses that $m \mapsto \lVert e(m)\rVert \, r_1^{m}$ and $m \mapsto \lVert e(m)\rVert \, r_2^{m}$ are summable over $m \in \mathbb{Z}$ (integer powers, so negative $m$ contribute $r_i^{m} = 1/r_i^{-m}$), and assume that for every $z \in \mathbb{C}$ with $r_1 < \lVert z\rVert$ and $\lVert z\rVert < r_2$ the unconditional sum $\sum_{m \in \mathbb{Z}} e(m) z^{m}$ equals $0$. The conclusion is the equality of functions $e = 0$, i.e. $e(m) = 0$ for every integer $m$. Note that the vanishing hypothesis is phrased with `tsum`, so it asserts that the value of the sum is $0$ at each point of the open annulus, summability there being a consequence of the two boundary hypotheses rather than an assumption.
--
--   This is the classical uniqueness of Laurent coefficients on an annulus, stated purely for absolutely convergent two-sided power series with no holomorphy assumption. It is used in the Langlands–Tunnell part of the development, where Rankin–Selberg local integrals are compared after being expanded into series in a complex parameter, to conclude that matching sums force matching coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
    (e : ℤ → ℂ) {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun m : ℤ => ‖e m‖ * r₁ ^ m) (hs₂ : Summable fun m : ℤ => ‖e m‖ * r₂ ^ m)
    (hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' m : ℤ, e m * z ^ m = 0) : e = 0 := by sorry
