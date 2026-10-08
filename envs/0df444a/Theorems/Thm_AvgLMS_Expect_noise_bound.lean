-- Prove2me | Theorems.Thm_AvgLMS_Expect_noise_bound
-- name    : AvgLMS.Expect.noise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:18.694653+00:00
-- url     : https://prove2.me/theorems/e23460a9-f5ce-49c0-bbef-363a56cc4352
-- title:
--   App. A.4, p. 15 — with η₀ = 0 and γR² < 1, (E⟨η̄ₙ₋₁, Hη̄ₙ₋₁⟩)^{1/2} ≤ (σ√d/√n)·1/(1 − √(γR²))
-- statement:
--   Assume (A1)–(A6) and let $\gamma>0$ with $\gamma R^2<1$. Let $\theta_n$ be the LMS iterates (1) started at $\theta_0=\theta^*$ (so $\eta_0=0$), and $\bar\eta_{n-1}=\bar\theta_{n-1}-\theta^*$. Then for every $n\ge1$,
--   $$\big(\mathbb E\langle\bar\eta_{n-1},H\bar\eta_{n-1}\rangle\big)^{1/2}\le\frac{\sigma\sqrt d}{\sqrt n}\cdot\frac{1}{1-\sqrt{\gamma R^2}},$$
--   and the expectation is finite.
--
--   This is the contribution of the noise to the final bound: the variance term $\sigma^2d/n$, up to a factor depending only on $\gamma R^2$, and in particular independent of the smallest eigenvalue of $H$.
--
--   **Formalization Note.** The section's assumption $\eta_0=0$ is encoded by starting the iterates at $\theta^*$. $\gamma>0$ and $n\ge1$ are added.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.4, last display, p. 15

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A.4, p. 15: with `η₀ = θ₀ − θ∗ = 0` (the LMS iterates started at `θ∗`) and `γR² < 1`,
`(E⟨η̄ₙ₋₁, H η̄ₙ₋₁⟩)^{1/2} ≤ (σ√d/√n) · 1/(1 − √(γR²))`. -/
theorem noise_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 < 1) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg (lmsIter γ θstar x z) (n - 1) ω - θstar,
      H (avg (lmsIter γ θstar x z) (n - 1) ω - θstar)⟫_ℝ) μ ∧
    Real.sqrt (∫ ω, ⟪avg (lmsIter γ θstar x z) (n - 1) ω - θstar,
        H (avg (lmsIter γ θstar x z) (n - 1) ω - θstar)⟫_ℝ ∂μ) ≤
      σ * Real.sqrt d / Real.sqrt n * (1 / (1 - Real.sqrt (γ * R ^ 2))) := by sorry
end AvgLMS.Expect
