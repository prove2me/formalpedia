-- Prove2me | Theorems.Thm_DPVerify_integral_bound
-- name    : DPVerify.integral_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:28.093805+00:00
-- url     : https://prove2.me/theorems/54910f8f-b45f-47eb-b5d7-a580e7dc0200
-- title:
--   Proof of Theorem 4.1, p.17 — $\mathbb E_r[p_t/(U_m(r)^2/\kappa^2+p_t^2)]\le\kappa\pi$ (corrected: the $\cot^{-1}$ identity for $p_t>0$)
-- statement:
--   Let $\kappa>0$, $L\ge1$, and let $u$ be uniform on $\{1/L,\dots,1\}$. Writing $\cot^{-1}(y)=\arctan(1/y)$ for $y>0$:
--
--   1. for $p\ge0$: $\displaystyle \mathbb E_u\Bigl[\frac{p}{u^2/\kappa^2+p^2}\Bigr]\le\int_0^1\frac{p}{u^2/\kappa^2+p^2}\,du\le\kappa\pi$;
--   2. for $p>0$: $\displaystyle \int_0^1\frac{p}{u^2/\kappa^2+p^2}\,du=\kappa\cot^{-1}(\kappa p)\le\kappa\pi$.
--
--   This bounds the rate at which the new verifier's acceptance probability changes along the interpolation between $(p_S,q_S)$ and their clipped versions, which turns the clipping bounds into the additive $120\pi\delta$ of Theorem 4.1.
--
--   Differences from the source:
--   - correction: $\int_0^1\frac{p_t}{u^2/\kappa^2+p_t^2}du=\kappa\cot^{-1}(\kappa p_t)$ → the identity for $p_t>0$; the bound $\le\kappa\pi$ for $p_t\ge0$; reason: at $p_t=0$ the integral is $0$ while $\kappa\cot^{-1}(0)=\kappa\pi/2$ under both conventions of footnote 7
--   - encoding: $\cot^{-1}$ with range $(-\pi/2,\pi/2]$ or $(0,\pi]$ (footnote 7) → $\arctan(1/y)$ for $y>0$; reason: both conventions agree with it for $y>0$
--   - encoding: $\mathbb E_r$ over $U_m(r)$ → the average over the grid $\{1/L,\dots,1\}$; reason: $U_m(r)$ is uniform on that grid
--   - generalization: $L\ge|\mathcal M|$ the smallest such power of two, a fixed constant $\kappa$, $p_t$ a probability → any integer $L\ge1$, any $\kappa>0$, any real $p\ge0$; reason: the page's values are instances; the bounds use only that the grid lies in $(0,1]$
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_DPVerify_gridMean

set_option autoImplicit false

namespace DPVerify

/-- §4, proof of Theorem 4.1, the integral display (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.17 = PDF p.20): for `κ > 0` and
`u ∼ Unif{1/L, …, 1}`,
`E_u [p / (u²/κ² + p²)] ≤ ∫₀¹ p / (u²/κ² + p²) du = κ cot⁻¹(κp) ≤ κπ`.
1. for `p ≥ 0`: the expectation is at most the integral, and the integral is at most `κπ`;
2. for `p > 0`: the integral equals `κ cot⁻¹(κp)`, which is at most `κπ`.

**Formalization Note** `cot⁻¹(y)` is `arctan(1/y)` for `y > 0`, where both conventions of footnote
7 agree. The equality is stated for `p > 0` only: at `p = 0` the integral is `0` while
`κ cot⁻¹(0) = κπ/2` (correction). -/
theorem integral_bound (κ : ℝ) (hκ : 0 < κ) (L : ℕ) (hL : 1 ≤ L) :
    (∀ p : ℝ, 0 ≤ p →
      gridMean L (fun u => p / (u ^ 2 / κ ^ 2 + p ^ 2)) ≤
        ∫ u in (0 : ℝ)..1, p / (u ^ 2 / κ ^ 2 + p ^ 2) ∧
      ∫ u in (0 : ℝ)..1, p / (u ^ 2 / κ ^ 2 + p ^ 2) ≤ κ * Real.pi) ∧
    (∀ p : ℝ, 0 < p →
      ∫ u in (0 : ℝ)..1, p / (u ^ 2 / κ ^ 2 + p ^ 2) = κ * Real.arctan (1 / (κ * p)) ∧
      κ * Real.arctan (1 / (κ * p)) ≤ κ * Real.pi) := by sorry

end DPVerify
