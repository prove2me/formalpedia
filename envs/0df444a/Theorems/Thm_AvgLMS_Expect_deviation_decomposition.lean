-- Prove2me | Theorems.Thm_AvgLMS_Expect_deviation_decomposition
-- name    : AvgLMS.Expect.deviation_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:54.688223+00:00
-- url     : https://prove2.me/theorems/92599b75-9a0d-45f2-805d-0c7738f455b4
-- title:
--   App. A.2, p. 13 — ηₙ = Mⁿ₁η₀ + γ Σₖ Mⁿₖ₊₁ξₖ with Mʲᵢ = (I − γxⱼ ⊗ xⱼ)⋯(I − γxᵢ ⊗ xᵢ)
-- statement:
--   Let $(x_n,z_n)$ be any observations, $\theta^*\in\mathcal H$, $\xi_n=z_n-\langle\theta^*,x_n\rangle x_n$ the residuals, and $\theta_n$ the LMS iterates (1) started at $\theta_0$, with deviations $\eta_n=\theta_n-\theta^*$. With the ordered products $M^j_i=(I-\gamma x_j\otimes x_j)\cdots(I-\gamma x_i\otimes x_i)$ and $M^{i-1}_i=I$, for every $n\ge0$ and every outcome,
--   $$\eta_n=M^n_1\eta_0+\gamma\sum_{k=1}^{n}M^n_{k+1}\xi_k .$$
--
--   The identity separates the deviation into a part driven by the initial condition and a part driven by the noise, which the proof bounds separately (Appendices A.3 and A.4).
--
--   **Formalization Note.** This is a pathwise algebraic identity, stated with no probabilistic hypothesis. $M^n_1$ is `Mprod γ x 1 n` and $M^n_{k+1}$ is `Mprod γ x (k + 1) (n − k)` with $k\le n$. Only this first identity of the paragraph is formalized; the averaged identity and the $L^p$ display that follow it are not.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.2, second paragraph, p. 13

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A.2, p. 13: `ηₙ = Mⁿ₁ η₀ + γ ∑_{k=1}^{n} Mⁿₖ₊₁ ξₖ`, with `ηₙ = θₙ − θ∗`,
`ξₖ = zₖ − ⟨θ∗, xₖ⟩ xₖ` and `Mʲᵢ = (I − γ xⱼ ⊗ xⱼ) ⋯ (I − γ xᵢ ⊗ xᵢ)`, `Mⁱ⁻¹ᵢ = I`.
In `Mprod` notation, `Mⁿ₁ = Mprod γ x 1 n` and `Mⁿₖ₊₁ = Mprod γ x (k + 1) (n − k)` (`k ≤ n`).
A deterministic identity, valid for every `ω`. -/
theorem deviation_decomposition {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (θstar θ0 : Hs d)
    (γ : ℝ) (n : ℕ) (ω : Ω) :
    lmsIter γ θ0 x z n ω - θstar =
      Mprod γ x 1 n ω (θ0 - θstar) +
        γ • ∑ k ∈ Finset.Icc 1 n, Mprod γ x (k + 1) (n - k) ω (residual x z θstar k ω) := by sorry
end AvgLMS.Expect
