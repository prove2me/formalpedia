-- Prove2me | Theorems.Thm_ActuarialValuation_aggregatePortfolioPMF_mass
-- name    : ActuarialValuation.aggregatePortfolioPMF_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:36:22.578879+00:00
-- url     : https://prove2.me/theorems/029d10e5-d10c-48c5-82a4-18c0e17dd6fe
-- title:
--   Every finite portfolio aggregate distribution is normalised
-- statement:
--   Starting with certain zero loss, each additional Bernoulli policy has unit probability mass. Convolution of supported unit-mass distributions preserves this property, yielding a properly normalised aggregate distribution across all possible losses up to the total benefits.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{s=0}^{B_n}g_n(s)=1
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregatePortfolioPMF
import Definitions.Def_actuarial_aggregateMaximumClaim
import Definitions.Def_actuarial_aggregateFiniteMass

namespace ActuarialValuation

theorem aggregatePortfolioPMF_mass (p : ℕ → ℝ) (b : ℕ → ℕ)
  (n : ℕ) :
  aggregateFiniteMass (aggregatePortfolioPMF p b n)
    (aggregateMaximumClaim b n) = 1 := by sorry

end ActuarialValuation
