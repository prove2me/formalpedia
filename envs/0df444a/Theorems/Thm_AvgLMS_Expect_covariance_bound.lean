-- Prove2me | Theorems.Thm_AvgLMS_Expect_covariance_bound
-- name    : AvgLMS.Expect.covariance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:12.782295+00:00
-- url     : https://prove2.me/theorems/816a2006-b7df-45ff-a272-04cdb29ecb13
-- title:
--   Eq. (17), p. 14 — for γR² ≤ 1, r ≥ 0 and n ≥ 2, E[ηʳₙ₋₁ ⊗ ηʳₙ₋₁] ≼ γ^{r+1}R^{2r}σ²I
-- statement:
--   Assume (A1)–(A6) and let $\gamma>0$ with $\gamma R^2\le1$. Let $\eta^r_n$ be the processes of Eq. (15) driven by the residuals $\xi_n$ and the inputs $x_n$, with $H$ the covariance operator. Then for every $r\ge0$ and $n\ge2$,
--   $$\mathbb E\big[\eta^r_{n-1}\otimes\eta^r_{n-1}\big]\preccurlyeq\gamma^{r+1}R^{2r}\sigma^2\,I .$$
--
--   The covariance of the order-$r$ term of the expansion decays geometrically in $r$ when $\gamma R^2<1$, which is what makes the expansion converge.
--
--   **Formalization Note.** The order is written as quadratic forms: for every $v$, $\mathbb E\langle\eta^r_{n-1},v\rangle^2\le\gamma^{r+1}R^{2r}\sigma^2\|v\|^2$, together with the integrability of the left integrand. $\gamma>0$ is added. The section's assumption $\eta_0=0$ plays no role, since every $\eta^r$ starts at $0$.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.4, Eq. (17), p. 14

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Eq. (17), App. A.4, p. 14: for `γR² ≤ 1`, every `r ≥ 0` and `n ≥ 2`,
`E[ηʳₙ₋₁ ⊗ ηʳₙ₋₁] ≼ γ^{r+1} R^{2r} σ² I`, written as the quadratic-form inequality
`E⟨ηʳₙ₋₁, v⟩² ≤ γ^{r+1} R^{2r} σ² ‖v‖²` for every `v`. -/
theorem covariance_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1) :
    ∀ r n : ℕ, 2 ≤ n → ∀ v : Hs d,
      Integrable (fun ω => ⟪etaR γ H x (residual x z θstar) r (n - 1) ω, v⟫_ℝ ^ 2) μ ∧
      ∫ ω, ⟪etaR γ H x (residual x z θstar) r (n - 1) ω, v⟫_ℝ ^ 2 ∂μ ≤
        γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 * ‖v‖ ^ 2 := by sorry
end AvgLMS.Expect
