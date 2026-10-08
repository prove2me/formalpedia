-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_mu_new_bounds
-- name    : CohenLeeSongLP.StochCentralPath.mu_new_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:00.011482+00:00
-- url     : https://prove2.me/theorems/70ba82ad-7009-4ec1-957a-d36640e8c60c
-- title:
--   Lemma 4.8 — bounds on $\mu^{\mathrm{new}}-\mu$
-- statement:
--   Let $n\ge 10$, let $A\in\mathbb R^{d\times n}$ have full row rank, and assume Assumption 4.1 (with $0<\epsilon\le 1/(40000\log n)$). Let $\widetilde\delta_\mu$ be the sample accepted by StochasticStep (conditioned law, which is a probability measure), $\mu=xs$, and
--   $$\mu_i^{\mathrm{new}}=(x_i+\widetilde\delta_{x,i})(s_i+\widetilde\delta_{s,i}).$$
--   Then
--   1. $\|\mathbf{E}[\mu^{-1}(\mu^{\mathrm{new}} - \mu - \widetilde{\delta}_\mu)]\|_2 \le 10\epsilon_{\mathrm{mp}} \cdot \epsilon$ and $\|\mathbf{E}[\mu^{-1}(\mu^{\mathrm{new}} - \mu)]\|_2 \le 5\epsilon$;
--   2. $\mathbf{Var}[\mu_i^{-1}\mu_i^{\mathrm{new}}] \le 50\epsilon^2/k$ for all $i$;
--   3. for every accepted sample, $\|\mu^{-1}(\mu^{\mathrm{new}} - \mu)\|_\infty \le \frac{0.021}{\log n}$.
--
--   These are the first- and second-moment bounds on the change of the duality measure that drive the expected decrease of the potential (Lemma 4.13).
--
--   **Formalization Note** As in Lemma 4.3, $\mathbf E$ and $\mathbf{Var}$ are under the conditioned law of the resampling loop, and the non-strict bound on $\epsilon$ replaces the printed $<$.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:14, Lemma 4.8 (Claims 4.9–4.11, pp. 3:14–3:16)

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.8 (p. 3:14) with Claims 4.9–4.11: under Assumption 4.1, for the sample `δ̃_μ`
accepted by StochasticStep (conditioned law, a probability measure), `μ = xs` and
`μ^new = (x + δ̃_x)(s + δ̃_s)`:
1. `‖E[μ⁻¹(μ^new − μ − δ̃_μ)]‖₂ ≤ 10 ε_mp ε` and `‖E[μ⁻¹(μ^new − μ)]‖₂ ≤ 5ε`;
2. `Var[μᵢ⁻¹ μᵢ^new] ≤ 50ε²/k` for all `i`;
3. for every accepted sample, `‖μ⁻¹(μ^new − μ)‖_∞ ≤ 0.021/log n`. -/
theorem mu_new_bounds {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v δμ : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ kSamp ε εmp) :
    IsProbabilityMeasure (stepLaw A x s v kSamp δμ) ∧
    norm2 (fun i => ∫ δ, (muNew A x s v δ i - x i * s i - δ i) / (x i * s i)
      ∂(stepLaw A x s v kSamp δμ)) ≤ 10 * εmp * ε ∧
    norm2 (fun i => ∫ δ, (muNew A x s v δ i - x i * s i) / (x i * s i)
      ∂(stepLaw A x s v kSamp δμ)) ≤ 5 * ε ∧
    (∀ i, variance (fun δ => muNew A x s v δ i / (x i * s i)) (stepLaw A x s v kSamp δμ)
      ≤ 50 * ε ^ 2 / kSamp) ∧
    (∀ δ ∈ successEvent A x s v, ∀ i,
      |(muNew A x s v δ i - x i * s i) / (x i * s i)| ≤ 0.021 / Real.log n) := by sorry

end CohenLeeSongLP.StochCentralPath
