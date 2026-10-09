-- Prove2me | Theorems.Thm_FastCLO_LowerBound_posterior_identity
-- name    : FastCLO.LowerBound.posterior_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:23.282578+00:00
-- url     : https://prove2.me/theorems/757b0ffe-f932-4504-bbde-a56c1802deae
-- title:
--   Proof of Theorem 3, p. 21 — the minimum posterior equals 1/(1 + ((1+ζ)/(1−ζ))^{|N¹ − N⁰|})
-- statement:
--   Let $0 \le \zeta < 1$ and let $N^0, N^1 \in \mathbb N$. Then
--   $$\frac{\min\Big\{\big(\tfrac{1+\zeta}{2}\big)^{N^1}\big(\tfrac{1-\zeta}{2}\big)^{N^0},\ \big(\tfrac{1+\zeta}{2}\big)^{N^0}\big(\tfrac{1-\zeta}{2}\big)^{N^1}\Big\}}{\big(\tfrac{1+\zeta}{2}\big)^{N^1}\big(\tfrac{1-\zeta}{2}\big)^{N^0} + \big(\tfrac{1+\zeta}{2}\big)^{N^0}\big(\tfrac{1-\zeta}{2}\big)^{N^1}} = \frac{1}{1 + \big(\tfrac{1+\zeta}{1-\zeta}\big)^{|N^1 - N^0|}}.$$
--
--   In the lower-bound construction the left side is the minimum of the posterior probabilities of $b_i = 1$ and $b_i = 0$ given the data, where $N^1_i$ and $N^0_i$ count the observations at $x_i$ with each of the two possible cost vectors. The identity shows that this posterior depends on the data only through $|N^1_i - N^0_i|$.
--
--   **Formalization Note** This is the second equality of the page's display. The hypothesis $\zeta < 1$ keeps $1 - \zeta \ne 0$; the proof uses $\zeta \le 1/2$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 3 (A.2), p. 21, the display after "Hence,"

import Mathlib

namespace FastCLO.LowerBound

/-- The posterior identity (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 3, p. 21, the
display after "Hence,"): with `a = (1+ζ)/2`, `c = (1−ζ)/2` and counts `N⁰, N¹`,
`min{a^{N¹}c^{N⁰}, a^{N⁰}c^{N¹}} / (a^{N¹}c^{N⁰} + a^{N⁰}c^{N¹}) = 1 / (1 + ((1+ζ)/(1−ζ))^{|N¹ − N⁰|})`.

Formalization Note: this is the second equality of the display (the first identifies the left side
with the minimum posterior probability). `ζ < 1` keeps `1 − ζ ≠ 0`; the proof uses `ζ ≤ 1/2`. -/
theorem posterior_identity (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ < 1) (N0 N1 : ℕ) :
    min (((1 + ζ) / 2) ^ N1 * ((1 - ζ) / 2) ^ N0) (((1 + ζ) / 2) ^ N0 * ((1 - ζ) / 2) ^ N1) /
        (((1 + ζ) / 2) ^ N1 * ((1 - ζ) / 2) ^ N0 + ((1 + ζ) / 2) ^ N0 * ((1 - ζ) / 2) ^ N1) =
      1 / (1 + ((1 + ζ) / (1 - ζ)) ^ (Int.natAbs ((N1 : ℤ) - N0))) := by sorry

end FastCLO.LowerBound
