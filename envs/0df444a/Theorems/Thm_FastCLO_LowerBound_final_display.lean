-- Prove2me | Theorems.Thm_FastCLO_LowerBound_final_display
-- name    : FastCLO.LowerBound.final_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:26.102405+00:00
-- url     : https://prove2.me/theorems/4668181c-f046-4213-b56e-425e835a12ac
-- title:
--   Proof of Theorem 7, p. 30 — with ζ = ((η−1)/n)^{1/(2+α)} ≤ ½, the bound becomes (ρ/2e⁴)((η−1)/n)^{(1+α)/(2+α)}
-- statement:
--   Let $\alpha \ge 0$, let $\eta \ge 2$ and $n$ be integers with $n \ge 2^{2+\alpha}(\eta - 1)$, let $\rho \ge 0$, and set $\zeta = \big(\tfrac{\eta-1}{n}\big)^{1/(2+\alpha)}$. Then
--   $$\frac{\zeta^{\alpha+1}\rho}{2}\exp\Big(-\frac{2\zeta}{1-\zeta}\sqrt{\frac{n\zeta^\alpha}{\eta-1}}\Big) \;\ge\; \frac{\rho}{2e^4}\Big(\frac{\eta-1}{n}\Big)^{\frac{1+\alpha}{2+\alpha}}.$$
--
--   This is the final calculation of the proof of Theorem 7: the choice of $\zeta$ balances the separation $\zeta\rho(\mathcal Z)$ of the hard instances against the information $n\zeta^\alpha/(\eta-1)$ the data carry about each hidden bit, and the condition on $n$ guarantees $\zeta \le 1/2$, so the exponential factor is at least $e^{-4}$.
--
--   **Formalization Note** The number $\rho$ stands for $\rho(\mathcal Z)$ and may be any nonnegative real. The hypothesis $\eta \ge 2$ is the page's implicit requirement for dividing by $\eta - 1$; together with the condition on $n$ it gives $n \ge 4$. All powers with real exponents are real powers of nonnegative bases.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 7 (A.4.4), p. 30, the display after "Finally, plugging in ζ"

import Mathlib

namespace FastCLO.LowerBound

/-- The final display of the proof of Theorem 7 (Hu, Kallus, Mao, arXiv:2011.03030v3, p. 30):
with `ζ = ((η−1)/n)^{1/(2+α)}` and `n ≥ 2^{2+α}(η − 1)`,
`(ζ^{α+1} ρ/2) exp(−(2ζ/(1−ζ)) √(nζ^α/(η−1))) ≥ (ρ/(2e⁴)) ((η−1)/n)^{(1+α)/(2+α)}`.

Formalization Note: `ρ` is any nonnegative real (the page has `ρ(Z)`). `2 ≤ η` because the page
divides by `η − 1`; it also forces `n ≥ 4 > 0`. All powers with real exponents are `Real.rpow` of
nonnegative bases. -/
theorem final_display (α : ℝ) (hα : 0 ≤ α) (η n : ℕ) (hη : 2 ≤ η)
    (hn : (2 : ℝ) ^ (2 + α) * ((η : ℝ) - 1) ≤ n) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let ζ : ℝ := (((η : ℝ) - 1) / n) ^ (1 / (2 + α))
    ρ / (2 * Real.exp 4) * (((η : ℝ) - 1) / n) ^ ((1 + α) / (2 + α)) ≤
      ζ ^ (α + 1) * ρ / 2 * Real.exp (-(2 * ζ / (1 - ζ)) * Real.sqrt (n * ζ ^ α / ((η : ℝ) - 1))) := by sorry

end FastCLO.LowerBound
