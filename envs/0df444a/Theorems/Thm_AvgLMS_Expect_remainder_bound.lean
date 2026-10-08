-- Prove2me | Theorems.Thm_AvgLMS_Expect_remainder_bound
-- name    : AvgLMS.Expect.remainder_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:22.558447+00:00
-- url     : https://prove2.me/theorems/608147f3-1abd-48fa-b5ac-656abab6beb4
-- title:
--   App. A.4, p. 15 — with η₀ = 0, γR² < 1: E⟨η̄ₙ₋₁ − Σ η̄ⁱₙ₋₁, H(η̄ₙ₋₁ − Σ η̄ⁱₙ₋₁)⟩ ≤ γ^{r+2}σ²R^{2r+4}/(1 − γR²)
-- statement:
--   Assume (A1)–(A6) and let $\gamma>0$ with $\gamma R^2<1$. Let $\theta_n$ be the LMS iterates (1) started at $\theta_0=\theta^*$ (so $\eta_0=0$), $\eta_n=\theta_n-\theta^*$, and $\eta^i_n$ the processes of Eq. (15) driven by the residuals. Then for every $r\ge0$ and $n\ge1$, the remainder $\rho=\bar\eta_{n-1}-\sum_{i=0}^{r}\bar\eta^i_{n-1}$ of the order-$r$ expansion satisfies
--   $$\mathbb E\langle\rho,H\rho\rangle\le\frac{1}{1-\gamma R^2}\,\gamma^{r+2}\sigma^2R^{2r+4},$$
--   and the expectation is finite.
--
--   The remainder bound does not decay in $n$ but vanishes as $r\to\infty$, so the expansion recovers the noise process in the limit.
--
--   **Formalization Note.** The section's assumption $\eta_0=\theta_0-\theta^*=0$ is encoded by starting the iterates at $\theta^*$. The page's standing assumption is $\gamma R^2\le1$; the strict $\gamma R^2<1$ is required here because the bound divides by $1-\gamma R^2$ (Lean's division by zero returns $0$, which would make the statement false at $\gamma R^2=1$). $\gamma>0$ and $n\ge1$ are added.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.4, "Putting things together", first display, p. 15

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A.4, "Putting things together", p. 15: with `η₀ = θ₀ − θ∗ = 0` (the LMS iterates started
at `θ∗`) and `γR² < 1`, for every `r ≥ 0` and `n ≥ 1`,
`E⟨η̄ₙ₋₁ − ∑_{i=0}^{r} η̄ⁱₙ₋₁, H(η̄ₙ₋₁ − ∑_{i=0}^{r} η̄ⁱₙ₋₁)⟩ ≤ γ^{r+2} σ² R^{2r+4} / (1 − γR²)`. -/
theorem remainder_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 < 1) (r n : ℕ) (hn : 1 ≤ n) :
    let rem : Ω → Hs d := fun ω =>
      (avg (lmsIter γ θstar x z) (n - 1) ω - θstar) -
        ∑ i ∈ Finset.range (r + 1), avg (etaR γ H x (residual x z θstar) i) (n - 1) ω
    Integrable (fun ω => ⟪rem ω, H (rem ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪rem ω, H (rem ω)⟫_ℝ ∂μ ≤
      1 / (1 - γ * R ^ 2) * γ ^ (r + 2) * σ ^ 2 * R ^ (2 * r + 4) := by sorry
end AvgLMS.Expect
