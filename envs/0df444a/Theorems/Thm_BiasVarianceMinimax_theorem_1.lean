-- Prove2me | Theorems.Thm_BiasVarianceMinimax_theorem_1
-- name    : BiasVarianceMinimax.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:44.52485+00:00
-- url     : https://prove2.me/theorems/751df1ac-aa7f-4297-bc5e-c733c4423b2e
-- title:
--   Theorem 1 — the asymptotic MSE of the sample average
-- statement:
--   Let $\hat\theta(\cdot)\in\Theta$ have constants $B$, $\sigma^2$, and let $\bar\theta_n$ be the average of $n$ independent runs at one parameter $\delta=\delta_n$. If $\lim_{n\to\infty}\delta_n n^\alpha=d>0$ for some $\alpha>0$, then
--
--   $$\mathbb E(\bar\theta_n-\theta)^2=d^{2q_1}B^2n^{-2\alpha q_1}+\frac{\sigma^2}{d^{2q_2}}n^{2\alpha q_2-1}+o\big(n^{-2\alpha q_1}+n^{2\alpha q_2-1}\big).$$
--
--   The choice $\alpha=1/(2(q_1+q_2))$ is optimal: $\max(-2\alpha q_1,\,2\alpha q_2-1)\ge -q_1/(q_1+q_2)$ for every $\alpha>0$, with equality exactly at that value. For that $\alpha$,
--
--   $$\mathbb E(\bar\theta_n-\theta)^2=\Big(d^{2q_1}B^2+\frac{\sigma^2}{d^{2q_2}}\Big)n^{-q_1/(q_1+q_2)}+o\big(n^{-q_1/(q_1+q_2)}\big).$$
--
--   This identifies the order and the constant of the baseline, which is the denominator of the risk ratio.
--
--   Differences from the source:
--   - reading: lim δn^α = d > 0 with α unconstrained in the statement → α > 0 and δₙ > 0; reason: p.8 has δ = Θ(n^−α) with α > 0; for α ≤ 0, δ does not tend to 0
--   - reading: "achieves the optimal MSE order" → the larger exponent is at least −q₁/(q₁+q₂), with equality exactly at α = 1/(2(q₁+q₂)); reason: this is the content of the first-order balance on p.8
--   - reading: σ²(δ) = Var(ε(δ)) with only its limit stated → finite variance at every δ > 0, a field of the class; reason: σ²(δ) is printed as a real function and a run at any positive δ can occur
--   - encoding: θ̂(δ) a random variable with independent runs → a law per δ > 0, with runs as coordinates under `Measure.pi` over `Fin n`; reason: the mean squared errors depend only on the laws; same class
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 1, p.9

import Mathlib
import Definitions.Def_BiasVarianceMinimax_mseBaseline

open Filter Topology Asymptotics

namespace BiasVarianceMinimax

/-- **Theorem 1** (baseline asymptotics). Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 1, p.9.

Three clauses: the expansion for a positive sequence `δₙ` with `δₙ n^α → d`; the claim that
`α = 1/(2(q₁+q₂))` achieves the optimal order; the expansion at that `α`.

**Formalization Note.** `α > 0` comes from `δ = Θ(n^(-α))`, p.8. Here `mseAverage M (δ n) n` is the
`MSE` of the average of `n` independent runs at the one parameter `δ n`, and `M.B`, `M.σsq` are
`B`, `σ²`. "Optimal order" is read as: the larger of the two exponents is at least `-q₁/(q₁+q₂)`,
with equality exactly at `α = 1/(2(q₁+q₂))`. -/
theorem theorem_1 (q₁ q₂ d : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hd : 0 < d)
    (M : SimulationOutput q₁ q₂) :
    (∀ (α : ℝ) (δ : ℕ → ℝ), 0 < α → (∀ n, 0 < δ n) →
      Tendsto (fun n : ℕ => δ n * (n : ℝ) ^ α) atTop (𝓝 d) →
      (fun n : ℕ => mseAverage M (δ n) n -
          (d ^ (2 * q₁) * M.B ^ 2 * (n : ℝ) ^ (-2 * α * q₁)
            + M.σsq / d ^ (2 * q₂) * (n : ℝ) ^ (2 * α * q₂ - 1)))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (-2 * α * q₁) + (n : ℝ) ^ (2 * α * q₂ - 1)) ∧
    (∀ α : ℝ, 0 < α →
      -(q₁ / (q₁ + q₂)) ≤ max (-2 * α * q₁) (2 * α * q₂ - 1) ∧
      (max (-2 * α * q₁) (2 * α * q₂ - 1) = -(q₁ / (q₁ + q₂)) ↔ α = 1 / (2 * (q₁ + q₂)))) ∧
    (∀ δ : ℕ → ℝ, (∀ n, 0 < δ n) →
      Tendsto (fun n : ℕ => δ n * (n : ℝ) ^ (1 / (2 * (q₁ + q₂)))) atTop (𝓝 d) →
      (fun n : ℕ => mseAverage M (δ n) n -
          (d ^ (2 * q₁) * M.B ^ 2 + M.σsq / d ^ (2 * q₂)) * (n : ℝ) ^ (-(q₁ / (q₁ + q₂))))
        =o[atTop] fun n : ℕ => (n : ℝ) ^ (-(q₁ / (q₁ + q₂)))) := by sorry

end BiasVarianceMinimax
