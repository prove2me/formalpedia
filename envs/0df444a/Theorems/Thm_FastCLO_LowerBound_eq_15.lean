-- Prove2me | Theorems.Thm_FastCLO_LowerBound_eq_15
-- name    : FastCLO.LowerBound.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:23.668888+00:00
-- url     : https://prove2.me/theorems/61fc18b9-2b22-4bc9-8507-119c20a57223
-- title:
--   Eq. (15), second inequality — ((1+ζ)/(1−ζ))^{−s} ≥ exp(−(2ζ/(1−ζ)) s)
-- statement:
--   Let $0 \le \zeta < 1$ and $s \ge 0$. Then
--   $$\Big(\frac{1+\zeta}{1-\zeta}\Big)^{-s} \;\ge\; \exp\Big(-\frac{2\zeta}{1-\zeta}\, s\Big).$$
--
--   This is the second inequality of Eq. (15), which the paper derives from $1 + x \le e^x$; it is applied with $s = \sqrt{n/\eta}$ in the proof of Theorem 3 and with $s = \sqrt{n\zeta^\alpha/(\eta-1)}$ in the proof of Theorem 7. It turns the Bayes-risk bound into an exponential whose exponent stays bounded once $\zeta$ is tuned to $n$.
--
--   **Formalization Note** The power is the real power of the positive base $(1+\zeta)/(1-\zeta)$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 3 (A.2), Eq. (15), p. 22; reused in the proof of Theorem 7, pp. 29–30

import Mathlib

namespace FastCLO.LowerBound

/-- The second inequality of (15) (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 3, p. 22;
reused in the proof of Theorem 7, pp. 29–30): for `0 ≤ ζ < 1` and `s ≥ 0`,
`((1+ζ)/(1−ζ))^{−s} ≥ exp(−(2ζ/(1−ζ)) s)`.

Formalization Note: the page applies it with `s = √(n/η)`; the power is `Real.rpow` of a positive
base. -/
theorem eq_15 (ζ s : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ < 1) (hs : 0 ≤ s) :
    Real.exp (-(2 * ζ / (1 - ζ)) * s) ≤ ((1 + ζ) / (1 - ζ)) ^ (-s) := by sorry

end FastCLO.LowerBound
