-- Prove2me | Theorems.Thm_AvgLMS_Expect_theorem_1
-- name    : AvgLMS.Expect.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:29.685866+00:00
-- url     : https://prove2.me/theorems/e16d2479-e879-40c6-b9a7-348f0bdc9875
-- title:
--   Theorem 1, p. 3 — for 0 < γ < 1/R², E[f(θ̄ₙ₋₁) − f(θ∗)] ≤ (1/2n)[σ√d/(1 − √(γR²)) + R‖θ₀ − θ∗‖/√(γR²)]²
-- statement:
--   Assume (A1)–(A6): i.i.d. observations $(x_n,z_n)$ in $\mathcal H=\mathbb R^d$ with finite second moments, invertible covariance operator $H=\mathbb E[x_n\otimes x_n]$, least-squares objective $f(\theta)=\tfrac12\mathbb E[\langle\theta,x_n\rangle^2-2\langle\theta,z_n\rangle]$ minimized at $\theta^*$, residual $\xi_n=z_n-\langle\theta^*,x_n\rangle x_n$, and constants $R,\sigma>0$ with $\mathbb E[\xi_n\otimes\xi_n]\preccurlyeq\sigma^2H$ and $\mathbb E[\|x_n\|^2x_n\otimes x_n]\preccurlyeq R^2H$. Let $\theta_n$ be the LMS iterates
--   $$\theta_n=\theta_{n-1}-\gamma\big(\langle\theta_{n-1},x_n\rangle x_n-z_n\big)$$
--   started at $\theta_0\in\mathcal H$ with a constant step size $0<\gamma<1/R^2$, and $\bar\theta_{n-1}=n^{-1}\sum_{k=0}^{n-1}\theta_k$. Then for every $n\ge1$,
--   $$\mathbb E\big[f(\bar\theta_{n-1})-f(\theta^*)\big]\le\frac{1}{2n}\left[\frac{\sigma\sqrt d}{1-\sqrt{\gamma R^2}}+R\|\theta_0-\theta^*\|\frac{1}{\sqrt{\gamma R^2}}\right]^2 ,$$
--   and the excess risk $f(\bar\theta_{n-1})-f(\theta^*)$ is integrable.
--
--   This is the main result of §2.1: averaged constant-step-size LMS attains the rate $O(1/n)$ for least-squares regression with no strong-convexity assumption, with a bound that does not depend on the smallest eigenvalue of $H$. The term $\sigma^2d/n$ is the statistically optimal variance term.
--
--   **Formalization Note.** The model is the predicate `LMSAssumptions` of the definitions file (Loewner inequalities as quadratic forms, integrability of every moment). The hypotheses $\gamma>0$ (a step size; $\sqrt{\gamma R^2}$ is a denominator) and $n\ge1$ (for $\bar\theta_{n-1}$ and $1/n$) are added. The integrability conjunct rules out a vacuous bound through Lean's value $0$ for the integral of a non-integrable function.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, Theorem 1 and Eq. (2), §2.1, p. 3

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Theorem 1, Eq. (2), §2.1, p. 3: under (A1)–(A6), for every constant step size `0 < γ < 1/R²`
and every `n ≥ 1`, the averaged LMS iterate `θ̄ₙ₋₁ = n⁻¹ ∑_{k=0}^{n-1} θₖ` satisfies
`E[f(θ̄ₙ₋₁) − f(θ∗)] ≤ (1/(2n)) [σ√d/(1 − √(γR²)) + R‖θ₀ − θ∗‖ · 1/√(γR²)]²`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ : γ < 1 / R ^ 2) (θ0 : Hs d) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => lsObjective μ x z (avg (lmsIter γ θ0 x z) (n - 1) ω) -
      lsObjective μ x z θstar) μ ∧
    ∫ ω, (lsObjective μ x z (avg (lmsIter γ θ0 x z) (n - 1) ω) - lsObjective μ x z θstar) ∂μ ≤
      1 / (2 * n) * (σ * Real.sqrt d / (1 - Real.sqrt (γ * R ^ 2)) +
        R * ‖θ0 - θstar‖ * (1 / Real.sqrt (γ * R ^ 2))) ^ 2 := by sorry
end AvgLMS.Expect
