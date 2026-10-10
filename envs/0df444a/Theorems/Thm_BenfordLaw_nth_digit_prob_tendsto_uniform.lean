-- Prove2me | Theorems.Thm_BenfordLaw_nth_digit_prob_tendsto_uniform
-- name    : BenfordLaw.nth_digit_prob_tendsto_uniform
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:37.196833+00:00
-- url     : https://prove2.me/theorems/2e6bf9a0-5bcd-437e-b0bb-d314c465b7c5
-- title:
--   The $n$-th digit becomes uniform as $n\to\infty$
-- statement:
--   For every digit $d\in\{0,\dots,9\}$,
--   $$\lim_{n\to\infty}\ \sum_{k=10^{n-2}}^{10^{n-1}-1}\log_{10}\!\left(1+\frac{1}{10k+d}\right) = \frac1{10}.$$
--
--   By the previous milestone, the left side is the Benford probability that $d$ is the $n$-th significant digit; so the distribution of the $n$-th digit approaches the uniform distribution on $\{0,\dots,9\}$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Generalization to digits beyond the first" ("The distribution of the n-th digit, as n increases, rapidly approaches a uniform distribution with 10% for each of the ten digits").

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem nth_digit_prob_tendsto_uniform (d : ℕ) (hd : d ≤ 9) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Ico (10 ^ (n - 2) : ℕ) (10 ^ (n - 1)),
        Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)))
      Filter.atTop (nhds (1 / 10)) := by sorry

end BenfordLaw
