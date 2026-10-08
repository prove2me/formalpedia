-- Prove2me | Theorems.Thm_AvgLMS_Expect_initial_conditions_bound
-- name    : AvgLMS.Expect.initial_conditions_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:54.871315+00:00
-- url     : https://prove2.me/theorems/b3b682ad-7d85-4159-9508-04ff5fb4b82f
-- title:
--   App. A.3, p. 13 — with ξₙ ≡ 0 and γR² ≤ 1, E⟨η̄ₙ₋₁, Hη̄ₙ₋₁⟩ ≤ ‖η₀‖²/(nγ)
-- statement:
--   Assume (A1)–(A6) and let $0<\gamma$ with $\gamma R^2\le1$. Let $\eta_0\in\mathcal H$ and let $\eta_n=(I-\gamma x_n\otimes x_n)\eta_{n-1}$ for $n\ge1$ — the deviation process when the residual is uniformly zero, driven by the model's inputs $x_n$. Then for every $n\ge1$,
--   $$\mathbb E\langle\bar\eta_{n-1},H\bar\eta_{n-1}\rangle\le\frac{\|\eta_0\|^2}{n\gamma},$$
--   where $\bar\eta_{n-1}=n^{-1}\sum_{k=0}^{n-1}\eta_k$, and the expectation is finite.
--
--   This is the contribution of the initial condition to the final bound: it decays as $1/n$ without any strong-convexity assumption.
--
--   **Formalization Note.** The section's assumption "$\xi_n$ is uniformly equal to zero" is encoded by the noise-free recursion itself. $\gamma>0$ and $n\ge1$ are added.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A.3, p. 13

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A.3, p. 13: with `ξₙ` uniformly zero, i.e. `ηₙ = (I − γ xₙ ⊗ xₙ) ηₙ₋₁` driven by the
model's `xₙ`, and `γR² ≤ 1`: `E⟨η̄ₙ₋₁, H η̄ₙ₋₁⟩ ≤ ‖η₀‖²/(nγ)`. -/
theorem initial_conditions_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1) (η0 : Hs d) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg (biasIter γ η0 x) (n - 1) ω,
      H (avg (biasIter γ η0 x) (n - 1) ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪avg (biasIter γ η0 x) (n - 1) ω, H (avg (biasIter γ η0 x) (n - 1) ω)⟫_ℝ ∂μ ≤
      ‖η0‖ ^ 2 / (n * γ) := by sorry
end AvgLMS.Expect
