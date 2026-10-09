-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSplitJointMass_factor
-- name    : ActuarialValuation.poissonSplitJointMass_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:14:52.730124+00:00
-- url     : https://prove2.me/theorems/48b768cf-b52f-47ef-b8a7-a1ec09fbbc90
-- title:
--   Poisson marked-stream joint mass factors into separate frequencies
-- statement:
--   The joint event of a selected arrivals and b other arrivals can be computed by conditioning a Poisson total on its binomial markings. Simplifying factorials and exponentials gives a product of two Poisson count masses at complementary thinned rates, establishing their independence at the joint-mass level.
--
--   **Mathematical statement**
--
--   $$
--   J(a,b)=p_{\lambda p}(a)p_{\lambda(1-p)}(b)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonSplitJointMass
import Definitions.Def_actuarial_poissonThinnedRate
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonSplitJointMass_factor
  (rate selection : ℝ) (a b : ℕ) :
  poissonSplitJointMass rate selection a b =
    poissonCountMass (poissonThinnedRate rate selection) a *
      poissonCountMass
        (poissonThinnedRate rate (1 - selection)) b := by sorry

end ActuarialValuation
