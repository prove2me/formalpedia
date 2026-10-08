-- Prove2me | Theorems.Thm_BoundedNV_Uniform_cor1_expected_order
-- name    : BoundedNV.Uniform.cor1_expected_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:41.835582+00:00
-- url     : https://prove2.me/theorems/431c08b0-9342-474f-b486-c599ae77d08b
-- title:
--   Corollary 1, p. 573 — under uniform demand E X♭ = μ − σ[φ(β′) − φ(α′)]/[Φ(β′) − Φ(α′)]
-- statement:
--   Let the demand $D$ be uniformly distributed on $[a, b]$ with $b > a \ge 0$, let $0 < c < p$, $\beta > 0$, and set
--   $$\mu = b - \frac{c}{p}(b-a), \qquad \sigma = \sqrt{\beta\,\frac{b-a}{p}}.$$
--   Then the expected behavioral solution is
--   $$\mathbb E X^\flat = \mu - \sigma\cdot\frac{\phi\big((b-\mu)/\sigma\big) - \phi\big((a-\mu)/\sigma\big)}{\Phi\big((b-\mu)/\sigma\big) - \Phi\big((a-\mu)/\sigma\big)},$$
--   where $\phi$ and $\Phi$ are the standard normal density and distribution function.
--
--   This closed form is the mean of the truncated normal law of Proposition 1 and is the input to Proposition 3 (midpoint bias).
--
--   **Formalization Note** $\mathbb E X^\flat$ is $\int_{\mathbb R} x\,\psi(x)\,dx$ with $\psi$ the logit density of the profit over $[a,b]$. $\phi$ is Mathlib's `gaussianPDFReal 0 1` and $\Phi$ the distribution function of `gaussianReal 0 1`. Since $a < b$ and $\sigma > 0$, the denominator is strictly positive, so the division is genuine.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 573 (PDF 8), Corollary 1, eq. (8)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit
import Definitions.Def_BoundedNV_Uniform_UniformDemand

open ProbabilityTheory

namespace BoundedNV.Uniform

/-- Corollary 1, p. 573: for demand `D ∼ U[a, b]`, the expected behavioral solution is the mean (8)
of the truncated normal law of Proposition 1,
`E X♭ = μ − σ (φ((b − μ)/σ) − φ((a − μ)/σ)) / (Φ((b − μ)/σ) − Φ((a − μ)/σ))`,
with `φ`, `Φ` the standard normal density and distribution function. -/
theorem cor1_expected_order (a b p c β μ σ : ℝ) (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c) (hcp : c < p)
    (hβ : 0 < β) (hμ : μ = unifMu a b p c) (hσ : σ = unifSigma a b p β) :
    logitExp (Set.Icc a b) (nvProfit (unifDensity a b) p c) β id =
      μ - σ * (gaussianPDFReal 0 1 ((b - μ) / σ) - gaussianPDFReal 0 1 ((a - μ) / σ)) /
        (cdf (gaussianReal 0 1) ((b - μ) / σ) - cdf (gaussianReal 0 1) ((a - μ) / σ)) := by sorry

end BoundedNV.Uniform
