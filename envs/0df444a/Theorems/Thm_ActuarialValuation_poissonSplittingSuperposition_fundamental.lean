-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSplittingSuperposition_fundamental
-- name    : ActuarialValuation.poissonSplittingSuperposition_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:25:59.570347+00:00
-- url     : https://prove2.me/theorems/404f11af-532a-40ad-beea-394a2783ac4a
-- title:
--   Poisson claim-type splitting and superposition identities
-- statement:
--   The capstone simultaneously formalises addition of independent Poisson claim-frequency streams and binomial splitting of one marked Poisson stream. It retains the exact joint count equality that characterises independence, rather than asserting it solely from matched marginal intensities.
--
--   **Mathematical statement**
--
--   $$
--   p_a*p_b=p_{a+b},\quad J_{\lambda,p}(i,j)=p_{\lambda p}(i)p_{\lambda(1-p)}(j)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountConvolution
import Definitions.Def_actuarial_poissonCountMass
import Definitions.Def_actuarial_poissonSuperposedRate
import Definitions.Def_actuarial_poissonSplitJointMass
import Definitions.Def_actuarial_poissonThinnedRate

namespace ActuarialValuation

theorem poissonSplittingSuperposition_fundamental
  (rate selection first second : ℝ)
  (n a b : ℕ)
  (hr : 0 ≤ rate) (hp0 : 0 ≤ selection) (hp1 : selection ≤ 1) :
  (poissonCountConvolution first second n =
     poissonCountMass (poissonSuperposedRate first second) n) ∧
  (poissonSplitJointMass rate selection a b =
     poissonCountMass (poissonThinnedRate rate selection) a *
       poissonCountMass
         (poissonThinnedRate rate (1 - selection)) b) := by sorry

end ActuarialValuation
