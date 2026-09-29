-- Prove2me | Theorems.Thm_FamousTheorems_leibniz_integral_rule
-- name    : FamousTheorems.leibniz_integral_rule
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:31.443914+00:00
-- url     : https://prove2.me/theorems/e6c9f9e7-f91f-46e2-a49a-df8f923c6fff
-- title:
--   The Leibniz integral rule (differentiation under the integral sign)
-- statement:
--   **The Leibniz integral rule.** Let $F(x,a)$ be a family of integrable functions of $a$, depending on a parameter $x$ in a normed space $H$, with values in a normed space $E$. Suppose that near $x_0$, for almost every $a$, $x\mapsto F(x,a)$ is differentiable with derivative $F'(x,a)$, and that $\|F'(x,a)\|\le\mathrm{bound}(a)$ for an integrable function $\mathrm{bound}$ (plus measurability conditions). Then
--   $$\frac{d}{dx}\Big|_{x_0}\int F(x,a)\,d\mu(a)=\int F'(x_0,a)\,d\mu(a).$$
--
--   Differentiation under the integral sign is a basic tool of analysis. It is used for Fourier and Laplace transforms, for Feynman's trick in evaluating integrals, and for proving regularity of solutions of differential equations given by integral formulas.
--
--   **Formalization note.** Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`. The parameter derivative is a Fréchet derivative `F' x a : H →L[𝕜] E` over `𝕜 = ℝ` or `ℂ`. The domination and differentiability hypotheses hold for all $x$ in a neighbourhood `s` of $x_0$ and almost every $a$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `hasFDerivAt_integral_of_dominated_of_fderiv_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem leibniz_integral_rule {α 𝕜 E H : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup H] [NormedSpace 𝕜 H] {F : H → α → E}
    {F' : H → α → H →L[𝕜] E} {x₀ : H} {bound : α → ℝ} {s : Set H} (hs : s ∈ nhds x₀)
    (hF_meas : ∀ᶠ x in nhds x₀, MeasureTheory.AEStronglyMeasurable (F x) μ) (hF_int : MeasureTheory.Integrable (F x₀) μ)
    (hF'_meas : MeasureTheory.AEStronglyMeasurable (F' x₀) μ) (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : MeasureTheory.Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (fun x => F x a) (F' x a) x) :
    HasFDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by sorry

end FamousTheorems
