-- Prove2me | Theorems.Thm_BenfordLaw_benford_mean_variance
-- name    : BenfordLaw.benford_mean_variance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:56.121781+00:00
-- url     : https://prove2.me/theorems/28a190a4-f89b-4d7b-96f3-cfd7cec3e32e
-- title:
--   Mean $3.440$ and variance $6.057$ of the Benford first digit
-- statement:
--   Let $D$ be a digit-valued random variable with the Benford distribution $\mathbb P(D=d) = \log_{10}(1+1/d)$, $d=1,\dots,9$. Then, to three decimal places,
--   $$\mathbb E[D] = \sum_{d=1}^9 d\,\log_{10}\!\left(1+\tfrac1d\right) \approx 3.440,\qquad \operatorname{Var}(D)=\sum_{d=1}^9 d^2\log_{10}\!\left(1+\tfrac1d\right)-\mathbb E[D]^2\approx 6.057.$$
--   Precisely: $|\mathbb E[D]-3.440|<0.0005$ and $|\operatorname{Var}(D)-6.057|<0.0005$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, section "Moments" (mean 3.440, variance 6.057).

import Mathlib
import Definitions.Def_BenfordLaw_Defs

namespace BenfordLaw

theorem benford_mean_variance :
    |(∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) * benfordProb 10 d) - 3.440| < 0.0005 ∧
      |((∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) ^ 2 * benfordProb 10 d) -
          (∑ d ∈ Finset.Icc (1 : ℕ) 9, (d : ℝ) * benfordProb 10 d) ^ 2) - 6.057| < 0.0005 := by sorry

end BenfordLaw
