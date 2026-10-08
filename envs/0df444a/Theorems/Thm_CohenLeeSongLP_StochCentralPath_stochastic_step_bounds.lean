-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_stochastic_step_bounds
-- name    : CohenLeeSongLP.StochCentralPath.stochastic_step_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:26:51.68571+00:00
-- url     : https://prove2.me/theorems/e8479fc9-bd83-4145-9586-c0892d82409f
-- title:
--   Lemma 4.3 — mean, variance and sup-norm bounds for the step of StochasticStep
-- statement:
--   Let $n\ge 10$, let $A\in\mathbb R^{d\times n}$ have full row rank, and let $x,s,t,\widetilde v,\delta_\mu,k,\epsilon,\epsilon_{\mathrm{mp}}$ satisfy Assumption 4.1 (with $0<\epsilon\le 1/(40000\log n)$). Let $\widetilde\delta_\mu$ be the sample accepted by the resampling loop of StochasticStep, i.e. distributed according to the product law of the sparse direction conditioned on the success event, and let $\widetilde\delta_x,\widetilde\delta_s$ be computed from it; write $\mu=xs$. Then this conditioned law is a probability measure, and the two vectors $\widetilde\delta_x$ and $\widetilde\delta_s$ found by StochasticStep satisfy:
--
--   1. $\|\mathbf{E}[\overline{s}^{-1}\widetilde{\delta}_s]\|_2 \le 2\epsilon$, $\|\mathbf{E}[\overline{x}^{-1}\widetilde{\delta}_x]\|_2 \le 2\epsilon$, $\|\mathbf{E}[s^{-1}\widetilde{\delta}_s]\|_2 \le 2\epsilon$, $\|\mathbf{E}[x^{-1}\widetilde{\delta}_x]\|_2 \le 2\epsilon$, $\|\mathbf{E}[\mu^{-1}\widetilde{\delta}_\mu]\|_2 \le 4\epsilon$;
--   2. for every $i$, $\mathbf{Var}[\frac{\widetilde{\delta}_{s,i}}{\overline{s}_i}] \le \frac{2\epsilon^2}{k}$, $\mathbf{Var}[\frac{\widetilde{\delta}_{x,i}}{\overline{x}_i}] \le \frac{2\epsilon^2}{k}$, $\mathbf{Var}[\frac{\widetilde{\delta}_{s,i}}{s_i}] \le \frac{2\epsilon^2}{k}$, $\mathbf{Var}[\frac{\widetilde{\delta}_{x,i}}{x_i}] \le \frac{2\epsilon^2}{k}$, $\mathbf{Var}[\frac{\widetilde{\delta}_{\mu,i}}{\mu_i}] \le \frac{8\epsilon^2}{k}$;
--   3. for every accepted sample,
--   $$\|\overline{s}^{-1}\widetilde{\delta}_s\|_\infty \le \frac{0.01}{\log n},\ \|s^{-1}\widetilde{\delta}_s\|_\infty \le \frac{0.02}{\log n},\ \|\overline{x}^{-1}\widetilde{\delta}_x\|_\infty \le \frac{0.01}{\log n},\ \|x^{-1}\widetilde{\delta}_x\|_\infty \le \frac{0.02}{\log n},\ \|\mu^{-1}\widetilde{\delta}_\mu\|_\infty \le \frac{0.02}{\log n}.$$
--
--   These bounds (Table 1 of the paper) are the inputs of the analysis of $\mu^{\mathrm{new}}$ (Lemma 4.8).
--
--   **Formalization Note** $\mathbf E$ of a vector is coordinatewise, and every $\mathbf E$ and $\mathbf{Var}$ is taken under the law *with* resampling (Remark 4.4 explains that the paper's proofs compute them without resampling, the difference being absorbed by the constants). The non-strict $\epsilon\le1/(40000\log n)$ replaces the printed $<$. Part 3 is stated for every sample in the success event.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:11, Lemma 4.3 (Claims 4.5–4.7, pp. 3:12–3:14; Remark 4.4)

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.3 (p. 3:11) with Claims 4.5–4.7: under Assumption 4.1, the law of the sample `δ̃_μ`
accepted by StochasticStep (the product law conditioned on the success event of the resampling
loop) is a probability measure, and for `δ̃_x, δ̃_s` and `μ = xs`:
1. `‖E[s̄⁻¹δ̃_s]‖₂, ‖E[x̄⁻¹δ̃_x]‖₂, ‖E[s⁻¹δ̃_s]‖₂, ‖E[x⁻¹δ̃_x]‖₂ ≤ 2ε` and `‖E[μ⁻¹δ̃_μ]‖₂ ≤ 4ε`;
2. for every `i`, the variances of `δ̃_{s,i}/s̄_i, δ̃_{x,i}/x̄_i, δ̃_{s,i}/s_i, δ̃_{x,i}/x_i` are at
   most `2ε²/k` and that of `δ̃_{μ,i}/μ_i` at most `8ε²/k`;
3. for every accepted sample, `‖s̄⁻¹δ̃_s‖_∞, ‖x̄⁻¹δ̃_x‖_∞ ≤ 0.01/log n` and
   `‖s⁻¹δ̃_s‖_∞, ‖x⁻¹δ̃_x‖_∞, ‖μ⁻¹δ̃_μ‖_∞ ≤ 0.02/log n`. -/
theorem stochastic_step_bounds {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v δμ : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ kSamp ε εmp) :
    IsProbabilityMeasure (stepLaw A x s v kSamp δμ) ∧
    -- Part 1
    norm2 (fun i => ∫ δ, stepS A x s v δ i / sbar x s v i ∂(stepLaw A x s v kSamp δμ))
      ≤ 2 * ε ∧
    norm2 (fun i => ∫ δ, stepX A x s v δ i / xbar x s v i ∂(stepLaw A x s v kSamp δμ))
      ≤ 2 * ε ∧
    norm2 (fun i => ∫ δ, stepS A x s v δ i / s i ∂(stepLaw A x s v kSamp δμ)) ≤ 2 * ε ∧
    norm2 (fun i => ∫ δ, stepX A x s v δ i / x i ∂(stepLaw A x s v kSamp δμ)) ≤ 2 * ε ∧
    norm2 (fun i => ∫ δ, δ i / (x i * s i) ∂(stepLaw A x s v kSamp δμ)) ≤ 4 * ε ∧
    -- Part 2
    (∀ i, variance (fun δ => stepS A x s v δ i / sbar x s v i) (stepLaw A x s v kSamp δμ)
      ≤ 2 * ε ^ 2 / kSamp) ∧
    (∀ i, variance (fun δ => stepX A x s v δ i / xbar x s v i) (stepLaw A x s v kSamp δμ)
      ≤ 2 * ε ^ 2 / kSamp) ∧
    (∀ i, variance (fun δ => stepS A x s v δ i / s i) (stepLaw A x s v kSamp δμ)
      ≤ 2 * ε ^ 2 / kSamp) ∧
    (∀ i, variance (fun δ => stepX A x s v δ i / x i) (stepLaw A x s v kSamp δμ)
      ≤ 2 * ε ^ 2 / kSamp) ∧
    (∀ i, variance (fun δ => δ i / (x i * s i)) (stepLaw A x s v kSamp δμ)
      ≤ 8 * ε ^ 2 / kSamp) ∧
    -- Part 3
    (∀ δ ∈ successEvent A x s v, ∀ i,
      |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
      |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
      |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
      |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
      |δ i / (x i * s i)| ≤ 0.02 / Real.log n) := by sorry

end CohenLeeSongLP.StochCentralPath
