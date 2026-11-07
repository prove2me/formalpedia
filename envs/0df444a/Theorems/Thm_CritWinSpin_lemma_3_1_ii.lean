-- Prove2me | Theorems.Thm_CritWinSpin_lemma_3_1_ii
-- name    : CritWinSpin.lemma_3_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:17.513874+00:00
-- url     : https://prove2.me/theorems/0db7ff06-c78d-44a0-a864-54a5d09bf48d
-- title:
--   Lemma 3.1(ii), p.11 — the fixed point $u$, its scale (12) and the quadratic gap (13)
-- statement:
--   Let $\rho$ be GHS of type $p$ and $q=2p-2$. There are $\theta_0,c,C>0$ such that for all $\theta\in(0,\theta_0]$ and $\beta=\tau+\theta$, the equation $u=\phi'(\beta u)$ has a unique solution $u\in(0,1)$, with
--   $$c\theta^{1/q}\le u\le C\theta^{1/q},\qquad\theta u^2=\Theta(\theta^{p/(p-1)}),$$
--   the global maxima of $F_\theta$ on $[-1,1]$ are attained at $\pm u$, and
--   $$F_\theta(u)-F_\theta(m)\ge c\theta(|m|-u)^2\quad\text{for all }m\in[-1,1].$$
--
--   This gives the concentration of each cloud in §6.
--
--   Differences from the source:
--   - encoding: θu² = Θ(θ^{p/(p−1)}) → two-sided bounds with the same constants c, C, uniform in θ ∈ (0, θ₀]; reason: constants can be merged by taking min and max
--   - encoding: global maxima at ±u → F_θ(−u) = F_θ(u) and F_θ(m) ≤ F_θ(u) on [−1, 1]; reason: the meaning of the phrase; (13) gives that they are the only maximisers
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 3.1(ii), p.11, eqs. (12), (13)

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 3.1(ii)** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.11). With
`q = 2p − 2`: for `θ ∈ (0, θ₀]` and `β = τ + θ`, the equation `u = ϕ'(βu)` has a unique solution in
`(0, 1)`, with `c θ^{1/q} ≤ u ≤ C θ^{1/q}` and `θu² = Θ(θ^{p/(p−1)})`, eq. (12); the global maxima of `F_θ`
on `[−1, 1]` are at `±u`; and `F_θ(u) − F_θ(m) ≥ c θ (|m| − u)²`, eq. (13). -/
theorem lemma_3_1_ii (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ θ₀ c C : ℝ, 0 < θ₀ ∧ 0 < c ∧ 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ u : ℝ, (0 < u ∧ u < 1 ∧ u = deriv (phi S) ((tau S + θ) * u)) ∧
        (∀ u' : ℝ, 0 < u' → u' < 1 → u' = deriv (phi S) ((tau S + θ) * u') → u' = u) ∧
        c * θ ^ (1 / (2 * (p : ℝ) - 2)) ≤ u ∧ u ≤ C * θ ^ (1 / (2 * (p : ℝ) - 2)) ∧
        c * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ≤ θ * u ^ 2 ∧
        θ * u ^ 2 ≤ C * θ ^ ((p : ℝ) / ((p : ℝ) - 1)) ∧
        Ftheta S θ (-u) = Ftheta S θ u ∧
        (∀ m : ℝ, |m| ≤ 1 → Ftheta S θ m ≤ Ftheta S θ u) ∧
        (∀ m : ℝ, |m| ≤ 1 → c * θ * (|m| - u) ^ 2 ≤ Ftheta S θ u - Ftheta S θ m) := by sorry

end CritWinSpin
