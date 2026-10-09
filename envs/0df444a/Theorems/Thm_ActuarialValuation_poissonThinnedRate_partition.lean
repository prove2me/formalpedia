-- Prove2me | Theorems.Thm_ActuarialValuation_poissonThinnedRate_partition
-- name    : ActuarialValuation.poissonThinnedRate_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:57:27.350527+00:00
-- url     : https://prove2.me/theorems/7b460b5d-90da-4b74-ab69-a28390eebb34
-- title:
--   Selected and unselected intensities add to original intensity
-- statement:
--   Each arrival is either selected or unselected, with complementary marking fractions. The algebraic sum of the resulting claim intensities reproduces the original Poisson claim frequency without loss or duplication.
--
--   **Mathematical statement**
--
--   $$
--   \lambda p+\lambda(1-p)=\lambda
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonThinnedRate

namespace ActuarialValuation

theorem poissonThinnedRate_partition (rate selection : ℝ) :
  poissonThinnedRate rate selection +
    poissonThinnedRate rate (1 - selection) = rate := by sorry

end ActuarialValuation
