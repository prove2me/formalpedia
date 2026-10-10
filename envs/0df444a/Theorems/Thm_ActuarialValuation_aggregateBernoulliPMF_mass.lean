-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateBernoulliPMF_mass
-- name    : ActuarialValuation.aggregateBernoulliPMF_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:31:55.192644+00:00
-- url     : https://prove2.me/theorems/e62228ce-9b6f-4ed1-b569-fd0d7870eecb
-- title:
--   A Bernoulli claim law has total mass one, even for zero benefit
-- statement:
--   Whether the policy benefit b is positive or zero, the no-claim and claim events exhaust the Bernoulli probability space. Summing across possible integer claim amounts up to b gives one, including when their two event labels both pay zero.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{s=0}^{b}h_{p,b}(s)=1
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateFiniteMass
import Definitions.Def_actuarial_aggregateBernoulliPMF

namespace ActuarialValuation

theorem aggregateBernoulliPMF_mass (p : ℝ) (b : ℕ) :
  aggregateFiniteMass (aggregateBernoulliPMF p b) b = 1 := by sorry

end ActuarialValuation
