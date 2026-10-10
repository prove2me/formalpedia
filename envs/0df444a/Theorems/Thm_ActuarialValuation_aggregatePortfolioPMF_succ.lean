-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_succ
-- name    : ActuarialValuation.aggregatePortfolioPMF_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:35:05.125994+00:00
-- url     : https://prove2.me/theorems/d81ee0e5-1a08-4058-ba8c-8b76c600b9cf
-- title:
--   Adding a policy applies one Bernoulli convolution
-- statement:
--   The portfolio distribution after adding policy n equals convolution of the previous n-policy aggregate distribution with that policy's Bernoulli amount. This exactly expresses independent aggregation while allowing benefit and occurrence probability to vary by policy.
--
--   **Mathematical statement**
--
--   $$
--   g_{n+1}=g_n*h_{p_n,b_n}
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateConvolution
import Definitions.Def_actuarial_aggregateBernoulliPMF

namespace ActuarialValuation

theorem aggregatePortfolioPMF_succ (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n s : ℕ) :
  aggregatePortfolioPMF p b (n + 1) s =
    aggregateConvolution (aggregatePortfolioPMF p b n)
      (aggregateBernoulliPMF (p n) (b n)) s := by sorry

end ActuarialValuation
