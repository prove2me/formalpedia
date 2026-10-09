-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSplitJointMass_nonneg
-- name    : ActuarialValuation.poissonSplitJointMass_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:24:07.51501+00:00
-- url     : https://prove2.me/theorems/dd72bcef-7a8e-421e-be39-5199e42775ad
-- title:
--   Valid marking probabilities yield nonnegative joint masses
-- statement:
--   The total Poisson count mass, binomial coefficient and powers of selected and complementary probabilities are nonnegative. Their product is therefore a genuine nonnegative joint coefficient for every pair of marked claim counts.
--
--   **Mathematical statement**
--
--   $$
--   \lambda\ge0,\ 0\le p\le1\Rightarrow J(a,b)\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonSplitJointMass

namespace ActuarialValuation

theorem poissonSplitJointMass_nonneg
  (rate selection : ℝ) (a b : ℕ)
  (hr : 0 ≤ rate) (hp0 : 0 ≤ selection) (hp1 : selection ≤ 1) :
  0 ≤ poissonSplitJointMass rate selection a b := by sorry

end ActuarialValuation
