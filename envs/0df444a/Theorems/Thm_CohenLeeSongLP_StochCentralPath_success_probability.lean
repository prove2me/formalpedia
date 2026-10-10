-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_success_probability
-- name    : CohenLeeSongLP.StochCentralPath.success_probability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:05.206994+00:00
-- url     : https://prove2.me/theorems/4ce13875-dba5-4460-95c0-7a5d1ba0e038
-- title:
--   Claim 4.7 — the resampling loop succeeds with probability at least $1-2n\exp(-0.003k/(\epsilon\sqrt n\log n))$
-- statement:
--   Let $n\ge 10$, let $A\in\mathbb R^{d\times n}$ have full row rank, and assume Assumption 4.1 (with $0<\epsilon\le 1/(40000\log n)$). Without resampling, i.e. for $\widetilde\delta_\mu$ drawn from the product law of the sparse direction (independent coordinates, $\widetilde\delta_{\mu,i}=\delta_{\mu,i}/p_i$ with probability $p_i$ and $0$ otherwise), that law is a probability measure and the following holds with probability at least $1-2n\exp\!\big(-\frac{0.003k}{\epsilon\sqrt n\log n}\big)$:
--   $$\|\overline{s}^{-1}\widetilde{\delta}_s\|_\infty \le \frac{0.01}{\log n}, \|s^{-1}\widetilde{\delta}_s\|_\infty \le \frac{0.02}{\log n}, \|\overline{x}^{-1}\widetilde{\delta}_x\|_\infty \le \frac{0.01}{\log n}, \|x^{-1}\widetilde{\delta}_x\|_\infty \le \frac{0.02}{\log n}, \|\mu^{-1}\widetilde{\delta}_\mu\|_\infty \le \frac{0.02}{\log n}.$$
--
--   In particular the success event of the resampling loop has positive probability under Main's parameters, so that conditioning on it is meaningful. (The paper adds "With resampling, it always holds", which is Part 3 of Lemma 4.3.)
--
--   **Formalization Note** The paper's "with probability $1-p$" is read as "with probability at least $1-p$". The probability is an `ENNReal` value compared with `ENNReal.ofReal` of the bound.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:13, Claim 4.7

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

open MeasureTheory ProbabilityTheory

namespace CohenLeeSongLP.StochCentralPath

/-- Claim 4.7 (p. 3:13): under Assumption 4.1, without resampling (for the product law of the
sparse direction `δ̃_μ`), with probability at least `1 − 2n exp(−0.003k/(ε√n log n))`,
`‖s̄⁻¹δ̃_s‖_∞, ‖x̄⁻¹δ̃_x‖_∞ ≤ 0.01/log n` and `‖s⁻¹δ̃_s‖_∞, ‖x⁻¹δ̃_x‖_∞, ‖μ⁻¹δ̃_μ‖_∞ ≤ 0.02/log n`.
The product law is a probability measure. -/
theorem success_probability {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v δμ : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ kSamp ε εmp) :
    IsProbabilityMeasure (sampleLaw kSamp δμ) ∧
    ENNReal.ofReal (1 - 2 * n * Real.exp (-(0.003 * kSamp / (ε * Real.sqrt n * Real.log n))))
      ≤ sampleLaw kSamp δμ {δ | ∀ i,
          |stepS A x s v δ i / sbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepS A x s v δ i / s i| ≤ 0.02 / Real.log n ∧
          |stepX A x s v δ i / xbar x s v i| ≤ 0.01 / Real.log n ∧
          |stepX A x s v δ i / x i| ≤ 0.02 / Real.log n ∧
          |δ i / (x i * s i)| ≤ 0.02 / Real.log n} := by sorry

end CohenLeeSongLP.StochCentralPath
