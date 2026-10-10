-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_nonneg
-- name    : ActuarialValuation.aggregateConvolution_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:31:14.953191+00:00
-- url     : https://prove2.me/theorems/06fae888-e4bc-4677-aae8-493cdb405bc7
-- title:
--   Convolution preserves nonnegative probability masses
-- statement:
--   Each summand is a product of nonnegative component probabilities. The finite sum of such products is nonnegative, which ensures that combining two valid discrete probability distributions cannot create negative aggregate mass.
--
--   **Mathematical statement**
--
--   $$
--   f,g\ge0\Longrightarrow f*g\ge0
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_nonneg (f g : ℕ → ℝ) (s : ℕ)
  (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) :
  0 ≤ aggregateConvolution f g s := by sorry

end ActuarialValuation
