-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_support
-- name    : ActuarialValuation.aggregatePortfolioPMF_support
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:35:45.87721+00:00
-- url     : https://prove2.me/theorems/177e1c32-0853-443e-aa3d-fb44837f21da
-- title:
--   Portfolio aggregate loss is bounded by total insured benefits
-- statement:
--   The total realised loss across n Bernoulli policies cannot exceed the sum of their individual maximum benefits. This exact finite-support identity follows by induction and support of convolution, including contracts with zero-benefit claims.
--
--   **Mathematical statement**
--
--   $$
--   s>B_n\Longrightarrow g_n(s)=0
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim

namespace ActuarialValuation

theorem aggregatePortfolioPMF_support (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n s : ℕ) (h : aggregateMaximumClaim b n < s) :
  aggregatePortfolioPMF p b n s = 0 := by sorry

end ActuarialValuation
