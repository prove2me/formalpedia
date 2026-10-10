-- Prove2me | Theorems.Thm_ActuarialValuation_poissonCountConvolution_superposition
-- name    : ActuarialValuation.poissonCountConvolution_superposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:10:22.780994+00:00
-- url     : https://prove2.me/theorems/a867425c-7441-473a-a134-7213c2d9b15e
-- title:
--   Convolution of independent Poisson counts is again Poisson
-- statement:
--   The count of combined independent Poisson processes has the Poisson coefficient with rate equal to the sum of their intensities. Expanding the convolution and applying the binomial theorem to the count powers yields the identity for every integer total n.
--
--   **Mathematical statement**
--
--   $$
--   \sum_{k=0}^np_a(k)p_b(n-k)=p_{a+b}(n)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountConvolution
import Definitions.Def_actuarial_poissonSuperposedRate
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonCountConvolution_superposition (a b : ℝ) (n : ℕ) :
  poissonCountConvolution a b n =
    poissonCountMass (poissonSuperposedRate a b) n := by sorry

end ActuarialValuation
