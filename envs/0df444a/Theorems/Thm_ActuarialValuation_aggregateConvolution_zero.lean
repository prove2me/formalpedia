-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_zero
-- name    : ActuarialValuation.aggregateConvolution_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:25:55.06955+00:00
-- url     : https://prove2.me/theorems/dca22c4e-6c39-4e13-992a-ec9c022fb527
-- title:
--   Convolution at loss zero multiplies the zero-loss masses
-- statement:
--   Only one nonnegative pair of integer component losses adds to zero: both component losses must equal zero. The coefficient of convolution at aggregate zero is therefore the product of their corresponding probability masses.
--
--   **Mathematical statement**
--
--   $$
--   (f*g)(0)=f(0)g(0)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_zero (f g : ℕ → ℝ) :
  aggregateConvolution f g 0 = f 0 * g 0 := by sorry

end ActuarialValuation
