-- Prove2me | Theorems.Thm_ActuarialValuation_pvPortfolioMean_succ
-- name    : ActuarialValuation.pvPortfolioMean_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:48.894563+00:00
-- url     : https://prove2.me/theorems/09b27507-f98e-40c9-8c41-695903995b9b
-- title:
--   Equivalence premiums and loss variance: pvPortfolioMean_succ
-- statement:
--   Increasing the finite portfolio by one policy adds its expected loss.
--
--   Mathematical relation:
--
--   $$
--   pvPortfolioMean\_succ
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPortfolioMean

namespace ActuarialValuation

theorem pvPortfolioMean_succ (means : ℕ → ℝ) (n : ℕ) : pvPortfolioMean means (n+1) = pvPortfolioMean means n + means n := by sorry

end ActuarialValuation
