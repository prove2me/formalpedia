-- Prove2me | Theorems.Thm_BenfordLaw_leadingDigits_prob_of_uniform_log_mantissa
-- name    : BenfordLaw.leadingDigits_prob_of_uniform_log_mantissa
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:02.117266+00:00
-- url     : https://prove2.me/theorems/59b0da4f-e075-4ee4-99fd-cf0bd6b20771
-- title:
--   First $k$ digits equal $n$ with probability $\log_{10}(1+1/n)$
-- statement:
--   Let $X$ be a positive random variable whose log-significand $\{\log_{10} X\}$ is uniformly distributed on $[0,1)$. Let $k\ge1$ and let $n$ be a $k$-digit integer, $10^{k-1}\le n<10^k$. Then the probability that $X$ starts with the string of digits $n$ (leading zeros discarded) is
--   $$\mathbb P\big(D^{(k)}_{10}(X) = n\big) = \log_{10}(n+1)-\log_{10}(n) = \log_{10}\!\left(1+\frac1n\right).$$
--
--   For example, the probability of starting with the digits $3,1,4$ is $\log_{10}(1+1/314)\approx 0.00138$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Generalization to digits beyond the first" (formula $\log_{10}(n+1)-\log_{10}(n)=\log_{10}(1+1/n)$, ref. Hill 1995, https://doi.org/10.1080/00029890.1995.11990578).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem leadingDigits_prob_of_uniform_log_mantissa {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (hX : HasUniformLogMantissa 10 P X)
    (k n : ℕ) (hk : 1 ≤ k) (hn1 : 10 ^ (k - 1) ≤ n) (hn2 : n < 10 ^ k) :
    (P {ω | leadingDigits 10 k (X ω) = n}).toReal = Real.logb 10 (1 + 1 / (n : ℝ)) := by sorry

end BenfordLaw
