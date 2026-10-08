-- Prove2me | Theorems.Thm_AvgLMS_Expect_order_r_bound
-- name    : AvgLMS.Expect.order_r_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:15.871827+00:00
-- url     : https://prove2.me/theorems/a6811367-7a33-4022-af50-48173d78e9e1
-- title:
--   App. A.4, p. 15 — for γR² ≤ 1, E⟨η̄ʳₙ₋₁, Hη̄ʳₙ₋₁⟩ ≤ (1/n)γʳR^{2r}dσ²
-- statement:
--   Assume (A1)–(A6) and let $\gamma>0$ with $\gamma R^2\le1$. Let $\eta^r_n$ be the processes of Eq. (15) driven by the residuals $\xi_n$, and $\bar\eta^r_{n-1}=n^{-1}\sum_{k=0}^{n-1}\eta^r_k$. Then for every $r\ge0$ and $n\ge1$,
--   $$\mathbb E\langle\bar\eta^r_{n-1},H\bar\eta^r_{n-1}\rangle\le\frac1n\,\gamma^rR^{2r}d\,\sigma^2 ,$$
--   and the expectation is finite.
--
--   Each term of the expansion of the noise process thus contributes at rate $1/n$, with a constant that decays geometrically in $r$.
--
--   **Formalization Note.** $d$ is the dimension of $\mathcal H=\mathbb R^d$. $\gamma>0$ and $n\ge1$ are added.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.4, "Putting things together", p. 15

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A.4, "Putting things together", p. 15: for `γR² ≤ 1`, every `r ≥ 0` and `n ≥ 1`,
`E⟨η̄ʳₙ₋₁, H η̄ʳₙ₋₁⟩ ≤ (1/n) γʳ R^{2r} d σ²`. -/
theorem order_r_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1) (r n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg (etaR γ H x (residual x z θstar) r) (n - 1) ω,
      H (avg (etaR γ H x (residual x z θstar) r) (n - 1) ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪avg (etaR γ H x (residual x z θstar) r) (n - 1) ω,
        H (avg (etaR γ H x (residual x z θstar) r) (n - 1) ω)⟫_ℝ ∂μ ≤
      1 / n * γ ^ r * R ^ (2 * r) * d * σ ^ 2 := by sorry
end AvgLMS.Expect
