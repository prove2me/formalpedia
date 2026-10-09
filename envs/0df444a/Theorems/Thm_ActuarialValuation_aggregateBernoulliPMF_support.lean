-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_support
-- name    : ActuarialValuation.aggregateBernoulliPMF_support
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:33:26.167802+00:00
-- url     : https://prove2.me/theorems/1d94b08d-379a-4ea4-b08a-d81a704394f6
-- title:
--   A Bernoulli policy never pays above its benefit
-- statement:
--   When the requested claim amount s exceeds the insured benefit b, it is neither zero nor the covered amount b. Both event contributions to the Bernoulli claim distribution vanish, regardless of the probability parameter.
--
--   **Mathematical statement**
--
--   $$
--   s>b\Longrightarrow h_{p,b}(s)=0
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateBernoulliPMF

namespace ActuarialValuation

theorem aggregateBernoulliPMF_support (p : ℝ) (b s : ℕ)
  (h : b < s) : aggregateBernoulliPMF p b s = 0 := by sorry

end ActuarialValuation
