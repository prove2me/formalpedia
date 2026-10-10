-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSuperposedRate_nonneg
-- name    : ActuarialValuation.poissonSuperposedRate_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:58:37.807679+00:00
-- url     : https://prove2.me/theorems/2897af55-9d76-4e94-adac-2bfae5f50ddb
-- title:
--   Nonnegative component frequencies imply nonnegative combined frequency
-- statement:
--   The intensity of a combined set of independent claim classes is the sum of their individual intensities. If both rates are legitimate nonnegative claim frequencies, the combined rate remains nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \lambda_1,\lambda_2\ge0\Rightarrow\lambda_1+\lambda_2\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonSuperposedRate

namespace ActuarialValuation

theorem poissonSuperposedRate_nonneg (a b : ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ poissonSuperposedRate a b := by sorry

end ActuarialValuation
