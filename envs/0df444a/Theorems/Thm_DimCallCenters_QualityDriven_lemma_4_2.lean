-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_4_2
-- name    : DimCallCenters.QualityDriven.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:35:22.429898+00:00
-- url     : https://prove2.me/theorems/227303f1-37f2-44a5-b3ee-d83dd2a8a0a8
-- title:
--   Lemma 4.2 (first statement) — $\pi_\lambda(x_\lambda) \approx Q_\lambda(x_\lambda)$ when $x_\lambda \to \infty$
-- statement:
--   Let $\mu > 0$ and let $x_\lambda > 0$ be a function of $\lambda > 0$ with $\lim_{\lambda\to\infty} x_\lambda = \infty$. Then the delay probability is asymptotically equivalent to its Stirling-type approximation $Q_\lambda$:
--
--   $$
--   \lim_{\lambda\to\infty}\frac{\pi_\lambda(x_\lambda)}{Q_\lambda(x_\lambda)} = 1 .
--   $$
--
--   This is the approximation behind the quality-driven staffing rule: when waiting is expensive the optimal staffing level grows faster than the square-root rule, and $Q_\lambda$ is the delay probability that the surrogate cost of Theorem 7.1 uses.
--
--   **Formalization Note** Only the first of the three statements of Lemma 4.2 is formalized. The second ("if also $x_\lambda \stackrel{\sup}{\le} \lambda^{1/6}$, then $\pi_\lambda(x_\lambda) \approx Q(x_\lambda)$") fails as printed at $x_\lambda = \lambda^{1/6}$, where the ratio tends to $e^{1/6}$; the third is not used by the mission's goal.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 16, Lemma 4.2 (first statement)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_QualityDriven_Qlam

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Lemma 4.2 (Appendix A), p. 16, first statement. For a positive function `x_λ` with
`x_λ → ∞` as `λ → ∞`, the delay probability is asymptotically equivalent to its Stirling-type
approximation: `π_λ(x_λ) ≈ Q_λ(x_λ)`, i.e. `π_λ(x_λ) / Q_λ(x_λ) → 1`. -/
theorem lemma_4_2 (μ : ℝ) (hμ : 0 < μ) (x : ℝ → ℝ) (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam)
    (hxinf : Tendsto x atTop atTop) :
    Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / Qlam μ lam (x lam)) atTop (𝓝 1) := by sorry

end DimCallCenters.QualityDriven
