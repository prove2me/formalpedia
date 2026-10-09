-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSuperposedRate_comm
-- name    : ActuarialValuation.poissonSuperposedRate_comm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:57:59.717953+00:00
-- url     : https://prove2.me/theorems/a09e4d9e-adc5-4217-a6ad-84ecdb991a1a
-- title:
--   Order of frequency streams does not affect total rate
-- statement:
--   The total count intensity depends only on the two constituent intensities, not on the order in which the underwriter combines them. This elementary symmetry underlies the distributional superposition identity.
--
--   **Mathematical statement**
--
--   $$
--   \lambda_1+\lambda_2=\lambda_2+\lambda_1
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonSuperposedRate

namespace ActuarialValuation

theorem poissonSuperposedRate_comm (a b : ℝ) :
  poissonSuperposedRate a b = poissonSuperposedRate b a := by sorry

end ActuarialValuation
