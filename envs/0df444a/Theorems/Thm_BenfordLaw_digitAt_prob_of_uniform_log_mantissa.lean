-- Prove2me | Theorems.Thm_BenfordLaw_digitAt_prob_of_uniform_log_mantissa
-- name    : BenfordLaw.digitAt_prob_of_uniform_log_mantissa
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:54.801878+00:00
-- url     : https://prove2.me/theorems/d9418e20-e429-4892-a336-cd23b84d37ab
-- title:
--   Distribution of the $n$-th significant digit
-- statement:
--   Let $X$ be a positive random variable whose log-significand $\{\log_{10}X\}$ is uniformly distributed on $[0,1)$. For every position $n\ge2$ and every digit $d\in\{0,1,\dots,9\}$, the probability that $d$ is the $n$-th significant digit of $X$ is
--   $$\mathbb P\big(\mathrm{dig}^{(n)}_{10}(X) = d\big) = \sum_{k=10^{n-2}}^{10^{n-1}-1}\log_{10}\!\left(1+\frac{1}{10k+d}\right).$$
--
--   For $n = 2$, $d = 2$ this is $\log_{10}(1+\tfrac1{12})+\log_{10}(1+\tfrac1{22})+\dots+\log_{10}(1+\tfrac1{92})\approx0.109$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Generalization to digits beyond the first" (formula for the probability that d is the n-th digit, n > 1).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem digitAt_prob_of_uniform_log_mantissa {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (hX : HasUniformLogMantissa 10 P X)
    (n : ℕ) (hn : 2 ≤ n) (d : ℕ) (hd : d ≤ 9) :
    (P {ω | digitAt 10 n (X ω) = d}).toReal =
      ∑ k ∈ Finset.Ico (10 ^ (n - 2) : ℕ) (10 ^ (n - 1)),
        Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) := by sorry

end BenfordLaw
