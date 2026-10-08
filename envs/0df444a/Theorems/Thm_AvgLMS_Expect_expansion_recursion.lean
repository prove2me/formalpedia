-- Prove2me | Theorems.Thm_AvgLMS_Expect_expansion_recursion
-- name    : AvgLMS.Expect.expansion_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:06:04.236597+00:00
-- url     : https://prove2.me/theorems/4c60e193-07ca-4aff-b742-2c967e519ed1
-- title:
--   Eq. (16), p. 14 — ηₙ − Σᵢ₌₀ʳ ηⁱₙ = (I − γxₙ ⊗ xₙ)(ηₙ₋₁ − Σᵢ₌₀ʳ ηⁱₙ₋₁) + γ(H − xₙ ⊗ xₙ)ηʳₙ₋₁
-- statement:
--   Let $(x_n,z_n)$ be any observations, $\theta^*\in\mathcal H$, $\xi_n$ the residuals, $\theta_n$ the LMS iterates (1) from any $\theta_0$, $\eta_n=\theta_n-\theta^*$, $H$ any operator, and $\eta^i_n$ the processes of Eq. (15) driven by $\xi_n$. Then for every $r\ge0$, every $n\ge1$ and every outcome,
--   $$\eta_n-\sum_{i=0}^{r}\eta^i_n=(I-\gamma x_n\otimes x_n)\Big(\eta_{n-1}-\sum_{i=0}^{r}\eta^i_{n-1}\Big)+\gamma(H-x_n\otimes x_n)\eta^r_{n-1}.$$
--
--   The remainder of the order-$r$ expansion therefore satisfies a recursion of the same type as $\eta_n$, with noise $\gamma(H-x_n\otimes x_n)\eta^r_{n-1}$, so Lemma 1 applies to it.
--
--   **Formalization Note.** The page prints $\sum_{i=0}^{r}\eta^r_{n-1}$ inside the first bracket; the two-line proof that follows uses $\sum_{i=0}^{r}\eta^i_{n-1}$, which is stated. The section's assumption $\eta_0=0$ and the choice of $H$ as the covariance operator are not needed for this pathwise identity and are dropped. The identity is stated at step $n+1$ with $n\ge0$.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.4, Eq. (16), p. 14

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Eq. (16), App. A.4, p. 14, with the sum `∑_{i=0}^{r} ηⁱₙ₋₁` (the page prints `ηʳₙ₋₁` inside
the sum): with `ηₙ = θₙ − θ∗` and `ηⁱ` the processes (15) driven by the residuals,
`ηₙ − ∑_{i=0}^{r} ηⁱₙ = (I − γ xₙ ⊗ xₙ)(ηₙ₋₁ − ∑_{i=0}^{r} ηⁱₙ₋₁) + γ (H − xₙ ⊗ xₙ) ηʳₙ₋₁`,
stated at step `n + 1`. A deterministic identity, valid for every `ω`, `θ₀`, `H`. -/
theorem expansion_recursion {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d)
    (θstar θ0 : Hs d) (γ : ℝ) (r n : ℕ) (ω : Ω) :
    (lmsIter γ θ0 x z (n + 1) ω - θstar) -
        ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i (n + 1) ω =
      (lmsIter γ θ0 x z n ω - θstar -
          ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i n ω) -
        γ • (⟪x (n + 1) ω, lmsIter γ θ0 x z n ω - θstar -
          ∑ i ∈ Finset.range (r + 1), etaR γ H x (residual x z θstar) i n ω⟫_ℝ • x (n + 1) ω) +
        γ • (H (etaR γ H x (residual x z θstar) r n ω) -
          ⟪x (n + 1) ω, etaR γ H x (residual x z θstar) r n ω⟫_ℝ • x (n + 1) ω) := by sorry
end AvgLMS.Expect
